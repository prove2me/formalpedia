-- Prove2me | solution 1 for GlobalTheory.BorelAlg.gen_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:30.388801+00:00
-- url     : https://prove2.me/submissions/41527155-b6a0-482b-b829-aee0272286b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6
import Theorems.Thm_GlobalTheory_BorelAlg_inj_block
import Theorems.Thm_GlobalTheory_BorelAlg_eval_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
namespace GlobalTheory.BorelAlg
theorem _root_.solution {τ τ' : ι} (h : τ ≠ τ') :
    IsRelPrime (gen m L τ).det (gen m L τ').det := by
  classical
  by_cases h0 : m τ = 0
  · haveI : IsEmpty (Fin (m τ)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  · have hi : Irreducible (gen m L τ).det := irreducible_det' h0 _ (inj_block m τ)
    rw [hi.isRelPrime_iff_not_dvd]
    intro hd
    haveI : Nonempty (Fin (m τ)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
    have := map_dvd (eval₂Hom (RingHom.id L)
      (fun p : Lt m => (fun t => if t = τ then (0 : Matrix (Fin (m t)) (Fin (m t)) L) else 1)
        p.1 p.2.1 p.2.2)) hd
    rw [eval_det m L _ (fun t => if t = τ then 0 else 1),
      eval_det m L _ (fun t => if t = τ then 0 else 1)] at this
    simp [h.symm] at this
end GlobalTheory.BorelAlg
