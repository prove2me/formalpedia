-- Prove2me | solution 1 for MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8414cd13-d199-54c6-9574-28c58c08102c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange

set_option autoImplicit false

universe u v

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det)
    (c : ℕ → Fin d → Fin d → R)
    (hc : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.frobenius (f i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (c m i j) (f j))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h) :
    letI : (Φ.map φ).IsComm := MvFormalGroup.isComm_map Φ φ
    IsUnit (Matrix.of fun i k =>
        MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.baseChange φ (f i)) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p (Φ.map φ),
        MvFormalGroup.CartierModule.frobenius (MvFormalGroup.CartierModule.baseChange φ (f i)) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (φ (c m i j))
              (MvFormalGroup.CartierModule.baseChange φ (f j)))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[N] h := by
  refine ⟨MvFormalGroup.CartierModule.isUnit_det_tangent_baseChangeEq (p := p) φ rfl f hf, ?_⟩
  intro i N
  obtain ⟨h, hh⟩ := hc i N
  refine ⟨MvFormalGroup.CartierModule.baseChange (p := p) φ h, ?_⟩
  have key := congrArg (MvFormalGroup.CartierModule.baseChange (p := p) φ) hh
  rw [MvFormalGroup.CartierModule.baseChangeEq_frobenius,
    MvFormalGroup.CartierModule.baseChangeEq_vExpansion (p := p) φ rfl N (fun m j => c m i j) f h] at key
  exact key

end S_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange (solution)
