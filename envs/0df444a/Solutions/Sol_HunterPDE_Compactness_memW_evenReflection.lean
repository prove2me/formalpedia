-- Prove2me | solution 1 for HunterPDE.Compactness.memW_evenReflection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:48:06.389712+00:00
-- url     : https://prove2.me/submissions/2870be66-1f0c-4f80-90e3-bf39bce71d11

import Theorems.Thm_MeasureTheory_MemLp_comp_abs_coordinate
import Theorems.Thm_HunterPDE_Shared_integral_evenReflection_mul_testFunction
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Lean.Elab.Tactic.Omega

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : HunterPDE.Compactness.MemW 1 p (HunterPDE.Compactness.upperHalfSpace m) f) :
    HunterPDE.Compactness.MemW 1 p Set.univ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      f (WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i))) := by
  classical
  let H := HunterPDE.Compactness.upperHalfSpace m
  let R : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun x => WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i)
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hzero : (fun _ : Fin (m + 1) => 0) ∈ HunterPDE.Compactness.multiIndicesLe (m + 1) 1 := by
    simp [HunterPDE.Compactness.multiIndicesLe, Fintype.mem_piFinset]
  have hDzero (φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
      HunterPDE.Shared.multiDeriv φ (fun _ => 0) = φ := by
    have hlist : HunterPDE.Shared.multiIndexList (fun _ : Fin (m + 1) => 0) = [] :=
      List.flatMap_eq_nil_iff.mpr (by intro j _; rfl)
    change HunterPDE.Shared.iteratedPartial φ
      (HunterPDE.Shared.multiIndexList (fun _ => 0)) = φ
    rw [hlist]
    rfl
  obtain ⟨g₀, hd₀, hg₀⟩ := hf _ hzero
  have hz : HunterPDE.Sobolev.HasWeakDeriv H (fun _ => 0) f g₀ := by
    refine ⟨hd₀.1, hd₀.2.1, ?_⟩
    intro φ hφ
    simpa [hDzero, HunterPDE.Sobolev.iteratedPartial] using hd₀.2.2 φ hφ
  have hfp : MemLp f p (volume.restrict H) :=
    hg₀.ae_eq (HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq hH hz)
  have hEF : MemLp (fun x => f (R x)) p volume :=
    MeasureTheory.MemLp.comp_abs_coordinate (m + 1) p (Fin.last m) f hfp
  have hEFli := hEF.locallyIntegrable hp
  intro α hα
  have hsum : ∑ i, α i ≤ 1 := (Finset.mem_filter.mp hα).2
  by_cases hzα : α = 0
  · subst α
    refine ⟨fun x => f (R x), ⟨hEFli.locallyIntegrableOn _, hEFli.locallyIntegrableOn _, ?_⟩, ?_⟩
    · intro φ _
      simp only [show (0 : Fin (m + 1) → ℕ) = (fun _ => 0) from rfl,
        hDzero, Finset.sum_const_zero, pow_zero, one_mul]
      rfl
    · simpa only [Measure.restrict_univ] using hEF
  have hex : ∃ i, α i ≠ 0 := by
    exact not_forall.mp (fun h => hzα (funext h))
  obtain ⟨i, hi⟩ := hex
  have hi1 : α i = 1 := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (α j)) (Finset.mem_univ i)
    omega
  have hαi : α = Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j; simp [hi1]
    · have hij : i ≠ j := Ne.symm hji
      have htwo : α i + α j ≤ ∑ k, α k := by
        simpa [hij] using Finset.sum_le_sum_of_subset_of_nonneg (f := α)
          (show {i, j} ⊆ Finset.univ from by simp) (fun _ _ _ => Nat.zero_le _)
      have hj : α j = 0 := by omega
      simp [Pi.single_eq_of_ne hji, hj]
  subst α
  obtain ⟨g, hd, hg⟩ := hf (Pi.single i 1) hα
  let G := fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
    if i = Fin.last m ∧ x (Fin.last m) < 0 then -g (R x) else g (R x)
  have hgR : MemLp (fun x => g (R x)) p volume :=
    MeasureTheory.MemLp.comp_abs_coordinate (m + 1) p (Fin.last m) g hg
  have hA : MeasurableSet {x : EuclideanSpace ℝ (Fin (m + 1)) |
      i = Fin.last m ∧ x (Fin.last m) < 0} :=
    (MeasurableSet.const _).inter
      (isOpen_lt (EuclideanSpace.proj (Fin.last m)).continuous continuous_const).measurableSet
  have hG : MemLp G p volume := by
    have hh := (hgR.neg.restrict _).piecewise hA (hgR.restrict _)
    apply hh.ae_eq
    exact Filter.Eventually.of_forall (fun x => by
      change (if x ∈ {x | i = Fin.last m ∧ x (Fin.last m) < 0} then
        -g (R x) else g (R x)) = G x
      by_cases hx : i = Fin.last m ∧ x (Fin.last m) < 0 <;> simp [G, hx])
  refine ⟨G, ⟨hEFli.locallyIntegrableOn _, (hG.locallyIntegrable hp).locallyIntegrableOn _, ?_⟩, ?_⟩
  · intro φ hφ
    simpa [G, R, Measure.restrict_univ] using
      HunterPDE.Shared.integral_evenReflection_mul_testFunction m p hp i f g hfp hg hd φ hφ
  · simpa only [Measure.restrict_univ] using hG
