-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.exists_polynomial_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:04.643582+00:00
-- url     : https://prove2.me/submissions/7d775d5c-5259-4357-a174-81ec3a3e0cd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Theorems.Thm_GlobalTheory_CompleteBaseChange_isPrecomplete_pi
import Theorems.Thm_GlobalTheory_CompleteBaseChange_isHausdorff_pi
import Theorems.Thm_GlobalTheory_CompleteBaseChange_mem_of_coeff_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {O σ τ : Type*} [CommRing O] [Finite σ] [Fintype τ]
    {J : Ideal O} (hJ : J.FG) [IsAdicComplete J O] (f : τ → MvPowerSeries σ O) (N : ℕ)
    (hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O))
    (g : MvPowerSeries σ O) :
    ∃ p : MvPolynomial σ O, g - p ∈ Ideal.span (Set.range f) := by
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  rw [← hx]
  exact (add_sub_cancel_left _ _).symm
end GlobalTheory.CompleteBaseChange
