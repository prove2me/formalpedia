-- Prove2me | solution 1 for MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/69a376b0-def1-5afa-9a26-8a2bbb7c2d8d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

import Theorems.Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_of_frobenius_expansion

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    (d : ℕ) (c : ℕ → Fin d → Fin d → R) :
    ∃ (Φ : MvFormalGroup d R) (_ : Φ.IsComm) (f : Fin d → MvFormalGroup.CartierModule p Φ),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.frobenius (f i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (c m i j) (f j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h := by
    classical
  obtain ⟨Φ₀, hΦ₀, f₀, hf₀, hc₀⟩ := MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X p d
  letI : Φ₀.IsComm := hΦ₀
  let φ : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p) →+* R :=
    MvPolynomial.eval₂Hom (algebraMap (PadicInt p) R) (fun v => c v.1 v.2.1 v.2.2)
  obtain ⟨hdet, hexp⟩ :=
    MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange p φ Φ₀ f₀ hf₀
      (fun m i j => (MvPolynomial.X ((m : ℕ), i, j) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)))
      (fun i N => hc₀ i N)
  refine ⟨Φ₀.map φ, MvFormalGroup.isComm_map Φ₀ φ, fun i => MvFormalGroup.CartierModule.baseChange φ (f₀ i),
    hdet, fun i N => ?_⟩
  obtain ⟨h, hh⟩ := hexp i N
  refine ⟨h, ?_⟩
  simpa only [φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] using hh

end S_MvFormalGroup_exists_cartierModule_vBasis_of_frobenius_expansion
end P2MW
export P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_of_frobenius_expansion (solution)
