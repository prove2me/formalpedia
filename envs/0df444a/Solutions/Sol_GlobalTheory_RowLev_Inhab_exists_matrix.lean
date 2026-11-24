-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:59.842728+00:00
-- url     : https://prove2.me/submissions/1915ff08-1dd6-4d41-8d7a-022c5210055c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution {R k L : Type} [CommRing R] [CommRing k] [AddCommGroup L] [Module R L] {N : ℕ}
    (r : R →+* k) (hr : Function.Surjective r) (c : L →ₛₗ[r] (Fin N → k)) (hc : Function.Surjective c)
    (𝔞 : Ideal R) (hk : ∀ y, c y = 0 ↔ y ∈ 𝔞 • (⊤ : Submodule R L)) (T : L →ₗ[R] L) :
    ∃ M : Matrix (Fin N) (Fin N) k, ∀ y, c (T y) = M *ᵥ c y := by
  classical
  have hT : ∀ y, c y = 0 → c (T y) = 0 := fun y hy => by
    rw [hk] at hy ⊢
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun z z' hz hz' => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [map_add]; exact add_mem hz hz'
  choose b hb using fun j : Fin N => hc (Pi.single j 1)
  choose s hs using hr
  refine ⟨Matrix.of fun i j => c (T (b j)) i, fun y => ?_⟩
  have h0 : c (y - ∑ j, s (c y j) • b j) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [map_smulₛₗ, hs, hb]
    exact pi_eq_sum_univ' _
  have h1 := hT _ h0
  rw [map_sub, map_sub, map_sum, map_sum, sub_eq_zero] at h1
  rw [h1]
  funext i
  simp only [map_smul, map_smulₛₗ, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.of_apply, mul_comm]
end GlobalTheory.RowLev.Inhab
