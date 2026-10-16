-- Prove2me | solution 1 for HunterPDE.Compactness.sobolevNorm_restrict_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:43:43.347845+00:00
-- url     : https://prove2.me/submissions/5b816abf-98a2-41c6-acf5-2dcee3173031

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ℝ≥0∞}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (h : f =ᵐ[volume.restrict Ω] F) :
    HunterPDE.Compactness.sobolevNorm k p Ω f ≤
      HunterPDE.Sobolev.sobolevNorm k p Set.univ F := by
  classical
  have happ (u : EuclideanSpace ℝ (Fin n) → ℝ) (a b : List (Fin n)) :
      HunterPDE.Shared.iteratedPartial u (a ++ b) =
        HunterPDE.Shared.iteratedPartial (HunterPDE.Shared.iteratedPartial u b) a := by
    induction a with
    | nil => rfl
    | cons i a ih => simp only [List.cons_append, HunterPDE.Shared.iteratedPartial, ih]
  have hrep (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (r : ℕ) :
      HunterPDE.Shared.iteratedPartial u (List.replicate r i) =
        (HunterPDE.Sobolev.partialDeriv i)^[r] u := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [List.replicate_succ, HunterPDE.Shared.iteratedPartial, ih,
        Function.iterate_succ_apply']
      rfl
  have hword (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ)
      (l : List (Fin n)) :
      HunterPDE.Shared.iteratedPartial u (l.flatMap (fun i => List.replicate (α i) i)) =
        l.foldr (fun i v => (HunterPDE.Sobolev.partialDeriv i)^[α i] v) u := by
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.flatMap_cons, happ, hrep, ih, List.foldr_cons]
  have hderiv (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
      HunterPDE.Shared.multiDeriv u α = HunterPDE.Sobolev.iteratedPartial α u :=
    hword u α (List.finRange n)
  have hsupport (u : EuclideanSpace ℝ (Fin n) → ℝ) (l : List (Fin n)) :
      tsupport (HunterPDE.Shared.iteratedPartial u l) ⊆ tsupport u := by
    induction l with
    | nil => exact Set.Subset.rfl
    | cons i l ih =>
      exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih
  have hindices : HunterPDE.Compactness.multiIndicesLe n k =
      HunterPDE.Sobolev.multiIndices n k := by
    ext α
    simp only [HunterPDE.Compactness.multiIndicesLe, HunterPDE.Sobolev.multiIndices,
      Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ha, hsum⟩
      exact ⟨⟨fun i => ⟨α i, ha i⟩, rfl⟩, hsum⟩
    · rintro ⟨⟨a, rfl⟩, hsum⟩
      exact ⟨fun i => (a i).isLt, hsum⟩
  have coord (α : Fin n → ℕ) (hα : α ∈ HunterPDE.Compactness.multiIndicesLe n k) :
      eLpNorm (HunterPDE.Shared.weakDeriv Ω α f) p (volume.restrict Ω) ≤
        eLpNorm (HunterPDE.Sobolev.weakDeriv Set.univ α F) p
          (volume.restrict Set.univ) := by
    have hdeg : ∑ i, α i ≤ k := (Finset.mem_filter.mp hα).2
    obtain ⟨g, hg, hgp⟩ := hF.2 α hdeg
    have hex : ∃ g, HunterPDE.Sobolev.HasWeakDeriv Set.univ α F g := ⟨g, hg⟩
    have hc : HunterPDE.Sobolev.HasWeakDeriv Set.univ α F
        (HunterPDE.Sobolev.weakDeriv Set.univ α F) := by
      unfold HunterPDE.Sobolev.weakDeriv
      rw [dif_pos hex]
      exact Exists.choose_spec hex
    let G := HunterPDE.Sobolev.weakDeriv Set.univ α F
    have hr : HunterPDE.Shared.HasWeakDeriv Ω α f G := by
      refine ⟨LocallyIntegrableOn.congr h.symm
        (hc.1.mono_set (Set.subset_univ _)), hc.2.1.mono_set (Set.subset_univ _), ?_⟩
      intro φ hφ
      have hw := hc.2.2 φ ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
      simp only [Measure.restrict_univ] at hw
      have hφzero (x) (hx : x ∉ Ω) : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ.2.2 hx'))
      have hd (x) (hx : x ∉ Ω) : HunterPDE.Shared.multiDeriv φ α x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hx' => hx (hφ.2.2 (hsupport φ _ hx')))
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hφzero x hx, mul_zero])]
      rw [integral_congr_ae (show (fun x => f x * HunterPDE.Shared.multiDeriv φ α x)
          =ᵐ[volume.restrict Ω] (fun x => F x * HunterPDE.Shared.multiDeriv φ α x) from
        h.mul (Filter.Eventually.of_forall fun _ => rfl))]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hd x hx, mul_zero])]
      simpa only [hderiv] using hw
    have he : ∃ g, HunterPDE.Shared.HasWeakDeriv Ω α f g := ⟨G, hr⟩
    have chosen : HunterPDE.Shared.HasWeakDeriv Ω α f
        (HunterPDE.Shared.weakDeriv Ω α f) := by
      unfold HunterPDE.Shared.weakDeriv
      rw [dif_pos he]
      exact Exists.choose_spec he
    rw [eLpNorm_congr_ae (chosen.ae_eq hΩ hr)]
    simpa only [Measure.restrict_univ] using
      eLpNorm_mono_measure (f := G) Measure.restrict_le_self
  unfold HunterPDE.Compactness.sobolevNorm HunterPDE.Sobolev.sobolevNorm
  split_ifs with hp
  · subst p
    rw [← hindices]
    exact Finset.sup_le fun α hα => (coord α hα).trans
      (Finset.le_sup (f := fun β =>
        eLpNorm (HunterPDE.Sobolev.weakDeriv Set.univ β F) ∞
          (volume.restrict Set.univ)) hα)
  · rw [← hindices]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact Finset.sum_le_sum fun α hα =>
      ENNReal.rpow_le_rpow (coord α hα) ENNReal.toReal_nonneg
