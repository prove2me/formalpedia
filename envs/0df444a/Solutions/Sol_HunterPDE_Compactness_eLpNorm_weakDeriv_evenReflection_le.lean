-- Prove2me | solution 1 for HunterPDE.Compactness.eLpNorm_weakDeriv_evenReflection_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:50:25.757882+00:00
-- url     : https://prove2.me/submissions/2199eb93-72e1-431c-b7e9-1e1e723bd089

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Theorems.Thm_MeasureTheory_eLpNorm_coordinate_evenReflection_le
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
    (hf : HunterPDE.Compactness.MemW 1 p (HunterPDE.Compactness.upperHalfSpace m) f)
    (α : Fin (m + 1) → ℕ)
    (hα : α ∈ HunterPDE.Compactness.multiIndicesLe (m + 1) 1) :
    eLpNorm (HunterPDE.Shared.weakDeriv Set.univ α (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      f (WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i)))) p (volume.restrict Set.univ) ≤
      2 * eLpNorm (HunterPDE.Shared.weakDeriv (HunterPDE.Compactness.upperHalfSpace m) α f)
        p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)) := by
  classical
  let H := HunterPDE.Compactness.upperHalfSpace m
  let R : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun x => WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i)
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hzero : (fun _ : Fin (m + 1) => 0) ∈ HunterPDE.Compactness.multiIndicesLe (m + 1) 1 := by
    simp [HunterPDE.Compactness.multiIndicesLe, Fintype.mem_piFinset]
  obtain ⟨g₀, hd₀, hg₀⟩ := hf _ hzero
  have hlistzero : (List.finRange (m + 1)).flatMap
      (fun _ => ([] : List (Fin (m + 1)))) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  have hz : HunterPDE.Sobolev.HasWeakDeriv H (fun _ => 0) f g₀ := by
    refine ⟨hd₀.1, hd₀.2.1, ?_⟩
    intro φ hφ
    simpa [HunterPDE.Shared.multiDeriv, HunterPDE.Shared.multiIndexList,
      hlistzero, HunterPDE.Shared.iteratedPartial, HunterPDE.Sobolev.iteratedPartial] using hd₀.2.2 φ hφ
  have h₀f := HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq hH hz
  have hfp : MemLp f p (volume.restrict H) := hg₀.ae_eq h₀f
  have hEF : MemLp (fun x => f (R x)) p volume :=
    MeasureTheory.MemLp.comp_abs_coordinate (m + 1) p (Fin.last m) f hfp
  have hEFli := hEF.locallyIntegrable hp
  have chosen {β : Fin (m + 1) → ℕ} {u v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
      (hv : HunterPDE.Shared.HasWeakDeriv Set.univ β u v) :
      HunterPDE.Shared.weakDeriv Set.univ β u =ᵐ[volume] v := by
    have he : ∃ w, HunterPDE.Shared.HasWeakDeriv Set.univ β u w := ⟨v, hv⟩
    have hc : HunterPDE.Shared.HasWeakDeriv Set.univ β u
        (HunterPDE.Shared.weakDeriv Set.univ β u) := by
      unfold HunterPDE.Shared.weakDeriv
      rw [dif_pos he]
      exact he.choose_spec
    simpa only [Measure.restrict_univ] using
      HunterPDE.Shared.HasWeakDeriv.ae_eq isOpen_univ hc hv
  have hsum : ∑ i, α i ≤ 1 := (Finset.mem_filter.mp hα).2
  by_cases hzα : α = 0
  · subst α
    have hdE : HunterPDE.Shared.HasWeakDeriv Set.univ 0 (fun x => f (R x))
        (fun x => f (R x)) := by
      refine ⟨hEFli.locallyIntegrableOn _, hEFli.locallyIntegrableOn _, ?_⟩
      intro φ _
      simp [HunterPDE.Shared.multiDeriv, HunterPDE.Shared.multiIndexList,
        hlistzero, HunterPDE.Shared.iteratedPartial]
    have hex : ∃ g, HunterPDE.Shared.HasWeakDeriv H 0 f g := ⟨g₀, hd₀⟩
    have hc : HunterPDE.Shared.HasWeakDeriv H 0 f (HunterPDE.Shared.weakDeriv H 0 f) := by
      unfold HunterPDE.Shared.weakDeriv
      rw [dif_pos hex]
      exact hex.choose_spec
    have hc₀ := HunterPDE.Shared.HasWeakDeriv.ae_eq hH hc hd₀
    have hcf := hc₀.trans h₀f
    change eLpNorm (HunterPDE.Shared.weakDeriv Set.univ 0 (fun x => f (R x))) p
      (volume.restrict Set.univ) ≤ 2 * eLpNorm (HunterPDE.Shared.weakDeriv H 0 f) p (volume.restrict H)
    rw [Measure.restrict_univ, eLpNorm_congr_ae (chosen hdE), eLpNorm_congr_ae hcf]
    exact MeasureTheory.eLpNorm_coordinate_evenReflection_le (Fin.last m) p hp f hfp.1
  have hex : ∃ i, α i ≠ 0 := by
    by_contra h
    push Not at h
    exact hzα (funext h)
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
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (s := {i, j}) (t := Finset.univ)
          (f := α) (by simp) (fun _ _ _ => Nat.zero_le _)
        simpa [hij] using hle
      have hj : α j = 0 := by omega
      simp [Pi.single_eq_of_ne hji, hj]
  subst α
  obtain ⟨g, hd, hg⟩ := hf (Pi.single i 1) hα
  let G := fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
    if i = Fin.last m ∧ x (Fin.last m) < 0 then -g (R x) else g (R x)
  have hgR : MemLp (fun x => g (R x)) p volume :=
    MeasureTheory.MemLp.comp_abs_coordinate (m + 1) p (Fin.last m) g hg
  have hA : MeasurableSet {x : EuclideanSpace ℝ (Fin (m + 1)) |
      i = Fin.last m ∧ x (Fin.last m) < 0} := by
    by_cases hi : i = Fin.last m
    · simp only [hi, true_and]
      exact (isOpen_lt (EuclideanSpace.proj (Fin.last m)).continuous continuous_const).measurableSet
    · simp [hi]
  have hG : MemLp G p volume := by
    have hh := (hgR.neg.restrict _).piecewise hA (hgR.restrict _)
    apply hh.ae_eq
    exact Filter.Eventually.of_forall (fun x => by
      change (if x ∈ {x | i = Fin.last m ∧ x (Fin.last m) < 0} then
        -g (R x) else g (R x)) = G x
      by_cases hx : i = Fin.last m ∧ x (Fin.last m) < 0 <;> simp [G, hx])
  have hdG : HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) (fun x => f (R x)) G := by
    refine ⟨hEFli.locallyIntegrableOn _, (hG.locallyIntegrable hp).locallyIntegrableOn _, ?_⟩
    intro φ hφ
    simpa [G, R, Measure.restrict_univ] using
      HunterPDE.Shared.integral_evenReflection_mul_testFunction m p hp i f g hfp hg hd φ hφ
  have hexg : ∃ w, HunterPDE.Shared.HasWeakDeriv H (Pi.single i 1) f w := ⟨g, hd⟩
  have hcg : HunterPDE.Shared.HasWeakDeriv H (Pi.single i 1) f
      (HunterPDE.Shared.weakDeriv H (Pi.single i 1) f) := by
    unfold HunterPDE.Shared.weakDeriv
    rw [dif_pos hexg]
    exact hexg.choose_spec
  have hcg' := HunterPDE.Shared.HasWeakDeriv.ae_eq hH hcg hd
  change eLpNorm (HunterPDE.Shared.weakDeriv Set.univ (Pi.single i 1) (fun x => f (R x))) p
      (volume.restrict Set.univ) ≤ 2 * eLpNorm (HunterPDE.Shared.weakDeriv H (Pi.single i 1) f) p (volume.restrict H)
  rw [Measure.restrict_univ, eLpNorm_congr_ae (chosen hdG), eLpNorm_congr_ae hcg']
  calc
    eLpNorm G p volume = eLpNorm (fun x => g (R x)) p volume := by
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp [G]; split_ifs <;> simp)
    _ ≤ 2 * eLpNorm g p (volume.restrict H) :=
      MeasureTheory.eLpNorm_coordinate_evenReflection_le (Fin.last m) p hp g hg.1
