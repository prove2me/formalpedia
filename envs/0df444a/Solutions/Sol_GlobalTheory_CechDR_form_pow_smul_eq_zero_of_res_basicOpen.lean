-- Prove2me | solution 1 for GlobalTheory.CechDR.form_pow_smul_eq_zero_of_res_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:29.398635+00:00
-- url     : https://prove2.me/submissions/11e1e21d-9e83-449a-8057-7085cb4be324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormPowSmulEqZeroOfResBasicOpen
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_eq_kaehlerDifferential_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩
end GlobalTheory.CechDR
