-- Prove2me | solution 1 for GlobalTheory.ArcTransport.GtRel.isIota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:44:13.262223+00:00
-- url     : https://prove2.me/submissions/917f2e07-0a98-4ad8-9f74-7397cd725a42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_injective
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_cP
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_iff
import Theorems.Thm_GlobalTheory_ArcTransport_rig_val
import Theorems.Thm_GlobalTheory_ArcTransport_tau_val
import Theorems.Thm_GlobalTheory_ArcTransport_psi_val
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
variable {he : eSec D'.P.A ≫ Φ = spMap f ≫ eSec D.P.A}
  (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
    (rigPullOf Φ (spMap f) he D.P.L D.rig))
include gp hT hc hw hr
namespace GlobalTheory.ArcTransport
namespace GtRel
theorem _root_.solution {u v : D.X → Fˣ} (hψ : ∀ χ, GenRel w (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F))
    (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) (v χ : F)) {x : D.X} (hu : ∀ χ, v (x + χ) = u χ * v x * v χ)
    {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) (H : GtPtF.IsIota x g₀) : GtPtF.IsIota (e x) g := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 H
  have hb : g.b = cP D' _ (e x) := pushF_injective gp hT (by rw [pushF_cP gp hT hc, b₁, ιb])
  refine (isIota_iff _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have ι₁ : vS (g₀.s χ) y J = vK (D.tau x χ) y J := ιv _ y J hJ
  show vS (g.s (e χ)) y J' = vK (D'.tau (e x) (e χ)) y J'
  have c₀ := v₁ χ y J J' hJ hJ'
  rw [ι₁, tau_val D _ _ hJ, rig_val gp hT hr hJ hJ',
    show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e (x + χ)) by rw [hb, map_add, cPoint_add, mul_comm],
    show wVal w y J J' g.b = wVal w y J J' (cP D' _ (e x)) by rw [hb]] at c₀
  have c₃ := psi_val hw (hψ (x + χ)) hJ hJ'
  rw [hu, map_mul, map_mul] at c₃
  rw [tau_val D' _ _ hJ', ← map_add]
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul c₀
  have a₁ := congrArg Additive.ofMul (psi_val hw (hψ x) hJ hJ')
  have a₂ := congrArg Additive.ofMul (psi_val hw (hψ χ) hJ hJ')
  have a₃ := congrArg Additive.ofMul c₃
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₀ + a₁ + a₂ - a₃
end GtRel
end GlobalTheory.ArcTransport
