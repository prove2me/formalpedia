-- Prove2me | solution 1 for GlobalTheory.w_cub_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:01.756005+00:00
-- url     : https://prove2.me/submissions/0e8a6937-484b-4b34-950d-46fe987af4e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
import Theorems.Thm_GlobalTheory_WCub_clause_iff
import Theorems.Thm_GlobalTheory_WCub_tripleProductPoint_comp_projection
import Theorems.Thm_P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83
import Theorems.Thm_GlobalTheory_WCub_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cub_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor WCub
set_option maxHeartbeats 1600000
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U
    : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf
    φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit)
    (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w'
    : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt'
    e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt'
    e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG
    I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt'
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I'
    e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w'
    e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫
    (fstG I' e G').left) z jL jL')) → ∀ (hgp : Geo.Tor.IsGrpPullback G' G (specOf φ) (bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) (c' : CubicalStr G' L'), Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ
    G (x3 G)) thε c'.t U.cubG.t (Geo.Tor.cubeMapOf hgp).F3 → ∀ (e : ℕ) (T : Over (Spec
    (CommRingCat.of (R' ⧸ I' ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R' I' e G')) (jL
    : thK → L'.L.ι) (jM : thK → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (lift ((Over.map (thick R' I'
    e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ≫ thφ G' (x3
    G') k) jL → LB.Coh D'.toPre.P.L (fun k => (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt'
    e).pG) (lift ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map
    (x 2) ≫ (gt' e).pG))).left ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM → ∀ (V : T.left.Opens) (hB
    : V ≤ (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) (lift ((Over.map (thick R' I'
    e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 2) ≫ (gt'
    e).pG))).left ⁻¹ᵁ (Theta D'.toPre.P.A D'.toPre.P.L).U jM) (hG : V ≤ (lift ((Over.map (thick R'
    I' e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ⁻¹ᵁ (Theta G' L'.L).U jL) (hw
    : ∀ k : thK, V ≤ (psum (thickObj R' I' e G') x k.down).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt'
    e).pG.left).U (fun _ => jM k) ⊓ (L'.L.pull (fstG I' e G').left).U
    (fun _ => jL k))), res hB (pullU _ _ (D'.toPre.cub.t.s jM)) = (∏ k : thK, res (hw k) (pullU
    (psum (thickObj R' I' e G') x k.down).left _ ((w' e).s
    (fun _ => jM k, fun _ => jL k))) ^ thε k) * res hG (pullU _ _ (c'.t.s jL)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL _ _ _ gt' w' _ _ H hgp c' hc e T x jL' jM' _ cM
  obtain ⟨h, h₁, ⟨h₂, -⟩, sq⟩ := H e
  have hgB := pull_grp hD
  have := (gt' e).q_hom
  have := (U.gt e).q_hom
  have mt : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have mf : Mono (fstG I e G).left := inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))
  have hs : ∀ i, ((x i).left ≫ h ≫ (thickObj R I e G).hom) ≫ thick R I e = T.hom ≫ thick R' I' e ≫ specOf φ := by
    intro i
    have a₁ : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom := (Over.w (fstG I e G)).symm
    have a₂ : (fstG I' e G').left ≫ G'.hom = (thickObj R' I' e G').hom ≫ thick R' I' e := Over.w (fstG I' e G')
    have a₃ := hgp.1.w
    rw [Category.assoc, Category.assoc, a₁, ← Category.assoc h, h₁, Category.assoc, a₃, ← Category.assoc _ G'.hom, a₂,
      ← Over.w (x i), Category.assoc, Category.assoc]
  let T₀ : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk ((x 0).left ≫ h ≫ (thickObj R I e G).hom)
  let x₀ : Fin 3 → (T₀ ⟶ thickObj R I e G) := fun i => Over.homMk ((x i).left ≫ h) (by
    rw [← cancel_mono (thick R I e)]
    exact ((congrArg (· ≫ thick R I e) (Category.assoc _ _ _)).trans (hs i)).trans (hs 0).symm)
  have f₁ := tri_thφ (thick R' I' e) (fstG I' e G') x (𝟙 _) (Category.id_comp _).symm
  have f₂ := tri_thφ (thick R' I' e) (gt' e).pG x (gt' e).q rfl
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x₀ (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x₀ (U.gt e).q rfl
  have g₁ : tri (thick R' I' e) (fstG I' e G') x ≫ (cubeMapOf hgp).F3 = tri (thick R I e) (fstG I e G) x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm
  have g₂ : tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3 = tri (thick R I e) (U.gt e).pG x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₂).trans (Category.assoc _ _ _).symm
  have k₁ : ∀ k : thK, (tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F =
      tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k := fun k => by
    rw [← g₁, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgp).psum_comm k.down)
  have k₂ : ∀ k : thK, (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F =
      tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k := fun k => by
    rw [← g₂, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgB).psum_comm k.down)
  have ph : ∀ k : thK, (psum (thickObj R I e G) x₀ k.down).left = (psum (thickObj R' I' e G') x k.down).left ≫ h :=
    fun k => by
      rw [← cancel_mono (fstG I e G).left]
      refine (f₃ k).symm.trans ((k₁ k).symm.trans ?_)
      rw [f₁ k, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h₁.symm
  refine (clause_iff (tri (thick R' I' e) (gt' e).pG x) (tri (thick R' I' e) (fstG I' e G') x)
    (fun k : thK => (psum (thickObj R' I' e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM') (c'.t.s jL')
    (fun k => (w' e).s (fun _ => jM' k, fun _ => jL' k)) thε).2 fun y hB hL hw => ?_
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB y _ jM' cM (fun k => Set.mem_iInter.1 hB k)
  choose J hJ using fun χ : T.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ y)
  let jM : thK → D.toPre.P.L.ι := fun k => J (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
  let jL : thK → U.LG.L.ι := fun k => N (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k)
  have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) y ∈ D.toPre.P.L.U (jM k) :=
    fun k => hJ _
  have mL : ∀ k, (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k) y ∈ U.LG.L.U (jL k) := fun k => hN _
  have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x₀) (tri (thick R I e) (fstG I e G) x₀)
    (fun k : thK => (psum (thickObj R I e G) x₀ k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
    (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
    (U.w_cub e T₀ x₀ jL jM (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
      have := mM k; rw [f₄ k] at this; exact this), mem_pull.2 (by
      have := mL k; rw [f₃ k] at this; exact this)⟩)
  have mL' : ∀ k, ((tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F) y ∈
      U.LG.L.U (jL k) := fun k => by rw [k₁ k]; exact mL k
  have mM' : ∀ k, ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F) y ∈
      D.toPre.P.L.U (jM k) := fun k => by rw [k₂ k]; exact mM k
  have e₃ := hc _ (tri (thick R' I' e) (fstG I' e G') x) y jL jL' mL' (fun k => Set.mem_iInter.1 hL k)
  rw [g₁] at e₃
  have e₁ := cub_pull hG hD (T' := (Over.map (thick R' I' e)).obj T) (z := y) (J := J) (J' := J') hJ hJ'
    ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG)
    ((Over.map (thick R' I' e)).map (x 2) ≫ (gt' e).pG)
  have v₁ : val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
      (tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3) y J =
      gm (tri (thick R I e) (U.gt e).pG x₀) y (LB.wchart _ (thφ D.toPre.P.A (x3 D.toPre.P.A)) jM)
        (D.toPre.cub.t.s jM) := by
    rw [g₂]; rfl
  have v₂ := val_of (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
    (tri (thick R' I' e) (gt' e).pG x) y J' jM' eJ'
  refine alg thε (fun k => gw hD.w ((psum (thickObj R' I' e G') x k.down).left ≫ (gt' e).pG.left) y (jM k) (jM' k))
    (fun k => gw (w' e) (psum (thickObj R' I' e G') x k.down).left y (jM' k) (fun _ => jL' k))
    (fun k => gw (U.w e) ((psum (thickObj R' I' e G') x k.down).left ≫ h) y (jM k) (fun _ => jL k))
    (fun k => gw wL ((psum (thickObj R' I' e G') x k.down).left ≫ (fstG I' e G').left) y (jL k) (jL' k))
    (fun k => sq _ _ y _ _ _ _ ?_ (mem_pull.1 (hw k).1) ?_ (mem_pull.1 (hw k).2))
    (v₁.symm.trans (e₁.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) v₂)))
    (e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
    (e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
  · have := mM' k
    rw [f₂ k] at this
    exact this
  · have := mL' k
    rw [f₁ k] at this
    exact this
  · show gw hD.w (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) y
      (J ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F))
      (J' (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k)) = _
    rw [k₂ k, eJ' k, f₂ k]
  · rw [← ph k]; rfl
  · rw [f₁ k]
end GlobalTheory
