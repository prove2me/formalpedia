-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/069c4a7e-cc11-50a1-adc4-6b3fd7d98795

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace P2MmfDrinModq

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem val_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  conv_lhs => rw [← hx]
  rw [← G.nsmul_natural f t x.1 x.2 n]
  rfl

theorem val_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id _)]
  rfl

theorem nsmul_eq_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t n x = G.one t ↔ x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 _)).1 := by
  rw [← val_nsmul, ← val_one]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end P2MmfDrinModq

open P2MmfDrinModq

theorem solution
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (hq : 2 ≤ q)
    (T : Type) [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) (hgg' : g.map (Int.castRingHom (ZMod q)) = g'.map (Int.castRingHom (ZMod q))) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ =
      ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x hΔ := by
  classical
  obtain ⟨V, P, Q⟩ := x
  obtain ⟨-, hΔ₁, hB⟩ := hx
  dsimp only at hΔ₁ hB
  set G : RelativeGroupLaw T (projModelStrCR V) := 𝒢 T V hΔ with hGdef
  have hBG : IsDrinfeldBasis G q P Q := hB
  have hBO := (WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q P Q).mp hBG
  obtain ⟨⟨pP, hpP⟩, ⟨pQ, hpQ⟩⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq G hq hBO

  set e : Spec (CommRingCat.of T) ⟶ projModelCR V := (G.one (𝟙 _)).1 with he_def
  have he : e ≫ projModelStrCR V = 𝟙 _ := (G.one (𝟙 _)).2

  have tors : ∀ (S : Section V) (p : Spec (CommRingCat.of T) ⟶ G.schemeKer q),
      p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = S.1 → G.nsmul (𝟙 _) q S = G.one (𝟙 _) := by
    intro S p hp
    have hsnd : p ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 = 𝟙 _ := by
      have h1 : (p ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1) ≫ e ≫ projModelStrCR V =
          S.1 ≫ G.schemeNsmul q ≫ projModelStrCR V := by
        rw [← Category.assoc, Category.assoc p, ← pullback.condition, ← Category.assoc, hp, Category.assoc]
      rw [he, Category.comp_id, G.schemeNsmul_over, S.2] at h1
      exact h1
    rw [nsmul_eq_one_iff, ← hp, Category.assoc, pullback.condition, ← Category.assoc, hsnd]
  have hPt := tors P pP hpP
  have hQt := tors Q pQ hpQ

  letI grp : Group (Section V) := G.pointGroup (𝟙 _)
  have hpow : ∀ (n : ℕ) (y : Section V), G.nsmul (𝟙 _) n y = y ^ n := by
    intro n y
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl
  have hzpow : ∀ (n : ℤ) (y : Section V), ModularCurve.LevelRelabelling.zsmulSection G n y = y ^ n := by
    intro n y
    cases n with
    | ofNat k =>
      show G.nsmul (𝟙 _) k y = y ^ ((k : ℕ) : ℤ)
      rw [hpow, zpow_natCast]
    | negSucc k =>
      show G.inv (𝟙 _) (G.nsmul (𝟙 _) (k + 1) y) = y ^ (Int.negSucc k)
      rw [hpow, zpow_negSucc]
      rfl
  have hzlin : ∀ a b : ℤ, ModularCurve.LevelRelabelling.zlinComb G P Q a b = P ^ a * Q ^ b := by
    intro a b
    show G.mul (𝟙 _) (ModularCurve.LevelRelabelling.zsmulSection G a P)
      (ModularCurve.LevelRelabelling.zsmulSection G b Q) = P ^ a * Q ^ b
    rw [hzpow, hzpow]
    rfl
  have hPq : P ^ q = 1 := by rw [← hpow]; exact hPt
  have hQq : Q ^ q = 1 := by rw [← hpow]; exact hQt

  have hent : ∀ i j : Fin 2, g i j % (q : ℤ) = g' i j % (q : ℤ) := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M i j) hgg'
    simp only [Matrix.map_apply, eq_intCast] at h
    exact (ZMod.intCast_eq_intCast_iff' _ _ q).mp h
  have key : ∀ a b a' b' : ℤ, a % (q : ℤ) = a' % (q : ℤ) → b % (q : ℤ) = b' % (q : ℤ) →
      ModularCurve.LevelRelabelling.zlinComb G P Q a b = ModularCurve.LevelRelabelling.zlinComb G P Q a' b' := by
    intro a b a' b' ha hb
    rw [hzlin, hzlin, zpow_eq_zpow_emod' a hPq, zpow_eq_zpow_emod' a' hPq, ha,
      zpow_eq_zpow_emod' b hQq, zpow_eq_zpow_emod' b' hQq, hb]
  unfold ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel
  dsimp only
  rw [key (g 0 0) (g 1 0) (g' 0 0) (g' 1 0) (hent 0 0) (hent 1 0),
    key (g 0 1) (g 1 1) (g' 0 1) (g' 1 1) (hent 0 1) (hent 1 1)]

end S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le (solution)
