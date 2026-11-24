-- Prove2me | solution 1 for GlobalTheory.UTrans.Chain.eventually_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:28.357972+00:00
-- url     : https://prove2.me/submissions/291ebb2b-a706-4706-aba2-3b2c70504965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Theorems.Thm_GlobalTheory_UTrans_Chain_eventually_aniso
import Theorems.Thm_GlobalTheory_UTrans_Chain_eventually_pair
import Theorems.Thm_GlobalTheory_T_quasiReflection_eq_mul_transvections_of_hyperbolicPlane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Chain
variable {E : Type} [Field E] [CharZero E] {n : ℕ}
namespace GlobalTheory.UTrans.Chain
theorem _root_.solution (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩
end GlobalTheory.UTrans.Chain
