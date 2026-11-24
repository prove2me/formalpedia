-- Prove2me | solution 1 for GlobalTheory.AdLat.hat_rational_points_and_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:18.401341+00:00
-- url     : https://prove2.me/submissions/9e831e4a-133b-4e98-a19e-162de082b366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_add
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_neg
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_zero
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_cap_gen_mem
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_mem
import Theorems.Thm_GlobalTheory_AdLat_cap_split
import Theorems.Thm_GlobalTheory_AdLat_cap_tmul_nsmul
import Theorems.Thm_GlobalTheory_AdLat_cap_exists_denom
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_adelicCompletion_fractionalIdeal_properties_alt
import Theorems.Thm_GlobalTheory_T_finiteAdele_strong_approximation_mod_nat
import Theorems.Thm_GlobalTheory_T_mem_adelicCompletion_pseudoBasis_iff
import Theorems.Thm_GlobalTheory_exists_pseudoBasis_adapted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L hfg hsp
  have h3 : ∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
    have hadd : ∀ z w : Fin n → RA F E, (∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, w - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, z + w - fv F x ∈ (hat F (L : Set (Fin n → E)))) := by
      rintro z w ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      have := add_mem hx hy
      rw [cap_fv_add]
      convert this using 1
      abel
    have hzero : ∃ x : Fin n → E, (0 : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) :=
      ⟨0, by rw [cap_fv_zero, sub_zero]; exact zero_mem _⟩
    have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (y : Fin n → E), ∃ x : Fin n → E,
        (fun i => a ⊗ₜ[F] y i : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro a y
      obtain ⟨d, hd, hy⟩ := cap_exists_denom L hsp y
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F d hd).1 a
      refine ⟨algebraMap F E r • y, ?_⟩
      rw [cap_split, add_sub_cancel_left, ← cap_tmul_nsmul]
      exact cap_gen_mem F _ a' ha' _ hy
    have hsingle : ∀ (i : Fin n) (t : RA F E), ∃ x : Fin n → E,
        (Pi.single i t : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul a y =>
        have := hgen a (Pi.single i y)
        convert this using 4
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      | add s t hs ht =>
        rw [Pi.single_add]
        exact hadd _ _ hs ht
    intro z
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ (fun z => ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))))
      hadd hzero (fun i _ => hsingle i (z i))
  refine ⟨?_, ?_, h3, ?_⟩
  · intro v
    obtain ⟨s, e, c, -, hc, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
    have hv : fv F v = ∑ a, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr v a) : RA F E) • fv F (e a) := by
      funext i
      have h := congrFun (e.sum_repr v) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [fv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
      rw [← TensorProduct.tmul_sum, h]
    rw [hv, GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff F E n L e c hc, hc]
    exact forall_congr' fun a => (GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 (c a) _
  · intro N hN z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F N hN).2 a ha
      refine ⟨algebraMap F E (r : F) • x, ?_, _, cap_gen_mem F _ a' ha' x hx, cap_split F _ _ _ _⟩
      exact L.smul_mem (algebraMap (𝓞 F) (𝓞 E) r) hx
    | zero => exact ⟨0, L.zero_mem, 0, zero_mem _, by simp [cap_fv_zero]⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      obtain ⟨x', hx', w', hw', rfl⟩ := hz'
      refine ⟨x + x', L.add_mem hx hx', w + w', add_mem hw hw', ?_⟩
      rw [cap_fv_add, smul_add]
      abel
    | neg z _ hz =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      refine ⟨-x, L.neg_mem hx, -w, neg_mem hw, ?_⟩
      rw [cap_fv_neg, smul_neg]
      abel
  · intro z
    obtain ⟨x, hx⟩ := h3 z
    obtain ⟨d, hd, hdx⟩ := cap_exists_denom L hsp x
    refine ⟨d, hd, ?_⟩
    have := add_mem (nsmul_mem hx d) (cap_fv_mem F (L : Set (Fin n → E)) _ hdx)
    rw [cap_fv_nsmul, ← smul_add, sub_add_cancel] at this
    exact this
end GlobalTheory.AdLat
