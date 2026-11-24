-- Prove2me | solution 1 for GlobalTheory.hermForm_pull_eq_of_lbIso_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:14.121632+00:00
-- url     : https://prove2.me/submissions/6e2f2455-9b90-4774-b606-604835557c34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Theorems.Thm_P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart
import Theorems.Thm_GlobalTheory_PullHermitian_idx_chart
import Theorems.Thm_GlobalTheory_PullHermitian_val_iso_pow
import Theorems.Thm_GlobalTheory_PullHermitian_exists_glue
import Theorems.Thm_GlobalTheory_PullHermitian_hermForm_pull
import Theorems.Thm_GlobalTheory_PullHermitian_hermForm_sub_smul
import Theorems.Thm_GlobalTheory_appellHumbert_trivial_of_nowhere_vanishing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open PullHermitian
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ z w, (m : ℂ) * hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF m n ⟨w, hw⟩
  have hFl : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by
    rw [hF, Over.comp_left]
  have hΛ : ∀ l : u.Λ, F l ∈ u'.Λ := fun l => by
    rw [← u'.ker, hF, (u.ker l).2 l.2, ← (u.ker 0).2 u.Λ.zero_mem, ← hF, map_zero]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩
      F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
    (fun p => (u.hol _ 0).1.inter ((u'.hol _ 0).1.preimage hFd.continuous))
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨(i, j), hi, hj⟩)
    (fun p z => valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val *
      u'.fr p.2 (F z) ^ m / u.fr p.1 z ^ n)
    (fun p => by
      have d1 := (u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2.mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        fun z hz => idx_chart _ _ _ _ _ _ hz.1 (hFl z ▸ hz.2)
      have d2 := (u'.fr_hol p.2).comp
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (u.fr_hol p.1).mono
        (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1} ∩ F ⁻¹' {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U p.2})
        Set.inter_subset_left
      simp only [div_eq_mul_inv]
      exact (d1.mul (d2.pow m)).mul
        ((d3.pow n).inv fun z hz => pow_ne_zero n (u.fr_ne p.1 z hz.1)))
    (fun p q z hp hq => by
      have h := val_iso_pow (u.ex z).left f.left m n w hw p.1 q.1 p.2 q.2 hp.1 hq.1
        (hFl z ▸ hp.2) (hFl z ▸ hq.2)
      have h1 := u.fr_compat p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u'.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [hFl] at h2
      rw [div_eq_div_iff (pow_ne_zero _ (u.fr_ne _ _ hp.1)) (pow_ne_zero _ (u.fr_ne _ _ hq.1)),
        h1, h2, mul_pow, mul_pow, ← _root_.mul_assoc, h]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * Hm' * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu'.1
  have hchart : ∀ z, ∃ i j, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j :=
    fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
      exact ⟨i, j, hi, hj⟩
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    ((n : ℂ) • Hm - (m : ℂ) • H₂) (fun l => χ l ^ n / χ' ⟨F l, hΛ l⟩ ^ m) r
    ((hu.1.smul (by simp [IsSelfAdjoint])).sub (hH₂h.smul (by simp [IsSelfAdjoint])))
    (fun l => by simp [hu.2.2.1, hu'.2.2.1]) hr
    (fun z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      rw [hrφ (i, j) z ⟨hi, hj⟩, valAt'_eq_unitVal _ (idx_chart _ _ _ _ _ _ hi (hFl z ▸ hj))]
      exact div_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne _ _ hj)))
        (pow_ne_zero _ (u.fr_ne _ _ hi)))
    (fun l z => by
      obtain ⟨i, j, hi, hj⟩ := hchart z
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have hj' : ⊤ ≤ (u'.ex (F (z + l))).left ⁻¹ᵁ L'.U j := by rwa [hF, hper, ← hF]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu'.2.2.2 ⟨F l, hΛ l⟩ j (F z) hj
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ' ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu'.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ (i, j) z ⟨hi, hj⟩, hrφ (i, j) (z + l) ⟨hi', hj'⟩]
      simp only [hper, hermForm_sub_smul, hH₂, hermForm_pull, map_add]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ Hm'.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ Hm'.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (n * a - m * a') + Real.pi / 2 * (n * b - m * b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) ^ n /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') ^ m := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      simp only [mul_pow]
      field_simp)
  intro z v
  have h := hermForm_sub_smul Hm H₂ n m z v
  rw [key.1, hH₂, hermForm_pull] at h
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h
  exact (sub_eq_zero.1 h.symm).symm
end GlobalTheory
