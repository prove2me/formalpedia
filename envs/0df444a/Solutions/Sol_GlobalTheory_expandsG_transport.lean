-- Prove2me | solution 1 for GlobalTheory.expandsG_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:48.572876+00:00
-- url     : https://prove2.me/submissions/af8e70ad-7e17-43de-8ca4-14a5c8a21fcf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
import Theorems.Thm_GlobalTheory_ExpGTrans_secLin_transport
import Theorems.Thm_P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9
import Theorems.Thm_P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707
import Theorems.Thm_GlobalTheory_SecPull_existsUnique_secPull
import Theorems.Thm_GlobalTheory_expandsAt_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ExpGTrans
set_option maxHeartbeats 1600000
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (U'
    : UnifPre I' D' A' G') (wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom
    (specOf φ)))), wL.IsGen → (∀ e : ℕ, ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e
    G).left, h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf
    φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt
    e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R'
    I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt
    e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫
    h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (F : Type) [Field
    F] [Algebra (FractionRing R) F] [Algebra (FractionRing R')
    F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R)
    r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF
    D'.toPre F).left ⟶ (DegPre.BF D.toPre F).left), Θ ≫ (fst (TF (R := R) F)
    D.toPre.P.A).left = (fst (TF (R := R') F) D'.toPre.P.A).left → Θ ≫ (DegPre.prB D.toPre
    F).left = (DegPre.prB D'.toPre F).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ)) → ∀ (Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left), Ξ ≫ (fst (TFK (R :=
    R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj
    G')).left → Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)) → ∀ (k : ℕ) (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s'
    : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (p
    : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, ((bc.hom.left ≫ pullback.fst G.hom (specOf
    φ))) ((fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z)) ∈ U.LG.L.U (p
    κ)) → (∀ κ, (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z) ∈ U'.LG.L.U (q
    κ)) → Geo.Tor.gs (r ≫ Ξ) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) p) ((σ).f
    p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ) z (p κ) (q
    κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => UnifPre.gFK (G := G') F) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z
    : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F).left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q
    : Fin 4 → D'.toPre.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ))) ((DegPre.famφ D'.toPre F x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F
    x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (DegPre.famφ
    D.toPre F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre
    F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L
    (DegPre.famφ D'.toPre F x) q) ((s'.s x).f
    q))) → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hbc U U' wL hwL hthick F _ _ _ hF Θ hΘ1 hΘ2 Ξ hΞ1 hΞ2
    k σ σ' s s' hσ hs hE
  unfold UnifPre.ExpandsG at hE ⊢
  obtain ⟨n, c, σs, fs, hAt, hσlin, hslin⟩ := hE
  have exG := fun i => (GlobalTheory.SecPull.existsUnique_secPull G.left G'.left G.left G'.left U.LG.L U'.LG.L
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) U.LG.isLB U'.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (fun _ => by rw [Category.id_comp, Category.comp_id]) (σs i)).exists
  choose σ's hσ' using exG
  have exD := fun i (x : D'.toPre.X) => (GlobalTheory.SecPull.existsUnique_secPull D.toPre.P.A.left D'.toPre.P.A.left
    D.toPre.P.A.left D'.toPre.P.A.left D.toPre.P.L D'.toPre.P.L
    (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) D.toPre.P.isLB D'.toPre.P.isLB hD.w hD.w_gen
    (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k)
    (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) (fun κ => famφB_pull hD x κ)
    (fs i (hD.xe x))).exists
  choose f's hf' using exD
  refine ⟨n, c, σ's, f's, ?_, ?_, ?_⟩
  · intro i e
    obtain ⟨hh, hh1⟩ := hthick e
    exact expandsAt_transport R R' I I' D D' A A' G G' U U' _ hD.w hD.xe _ wL hD.w_gen hwL
      (fun x κ => famφB_pull hD x κ) e e k hh hh1 (σs i) (σ's i) (fs i) (f's i) (hσ' i) (hf' i) (hAt i e)
  · refine secLin_transport U.LG.isLB U'.LG.isLB wL _ _ _ _ _ _ _ Ξ _
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm)
      (fun _ => by rw [Category.id_comp, Category.comp_id]) hΞ2 _ _ ?_ _ _ _ _ hσ (fun i => hσ' i) hσlin
    intro i y
    rw [GlobalTheory.FieldBaseChange.gs_scal, GlobalTheory.FieldBaseChange.gs_scal, Category.assoc, hΞ1]
  · intro α'
    refine secLin_transport D.toPre.P.isLB D'.toPre.P.isLB hD.w _ _ _ _ _ _ _ Θ _
      (fun κ => famφ_eq D.toPre F (hD.xe α') κ) (fun κ => famφ_eq D'.toPre F α' κ)
      (fun κ => famφB_pull hD α' κ) hΘ2 _ _ ?_ _ _ _ _ (hs α') (fun i => hf' i α') (hslin (hD.xe α'))
    intro i y
    rw [GlobalTheory.FieldBaseChange.gs_scal, GlobalTheory.FieldBaseChange.gs_scal, Category.assoc, hΘ1]
end GlobalTheory
