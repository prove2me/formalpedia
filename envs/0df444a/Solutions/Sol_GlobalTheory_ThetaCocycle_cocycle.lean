-- Prove2me | solution 1 for GlobalTheory.ThetaCocycle.cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:17.590508+00:00
-- url     : https://prove2.me/submissions/26854bcd-8e6a-417c-858d-1ff4464b3943

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Theorems.Thm_GlobalTheory_ThetaCocycle_PullsBack_comp
import Theorems.Thm_GlobalTheory_ThetaCocycle_PullsBack_cancel
import Theorems.Thm_GlobalTheory_CoverGlue_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaCocycle
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
namespace GlobalTheory.ThetaCocycle
theorem _root_.solution : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  intro hex o _ g n J β S s I U t u a b ha hb hrig i j m T x y z hxy hxz
  have HA : ∀ i j, PullsBack (u i j) (t i) (S.homOfLE inf_le_left) (a i j) := ha
  have HB : ∀ i j, PullsBack (u i j) (t j) (S.homOfLE inf_le_right) (b i j) := hb
  let V : S.Opens := (U i ⊓ U j) ⊓ (U j ⊓ U m)
  have hVm : V ≤ U m := inf_le_right.trans inf_le_right
  have hVim : V ≤ U i ⊓ U m := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨t', φk, gk, lk, pk, -⟩ := hex o g n J β (U m).toScheme V.toScheme ((U m).ι ≫ s)
    (S.homOfLE hVm ≫ (U m).ι ≫ s) (S.homOfLE hVm) (t m) rfl
  have hk : PullsBack t' (t m) (S.homOfLE hVm) φk := ⟨gk, lk, pk⟩
  obtain ⟨c₁, h₁, e₁⟩ := PullsBack.cancel (S.homOfLE (inf_le_right : V ≤ U j ⊓ U m)) hk (HB j m) (by simp)
  have h₁' : PullsBack t' (t j) (S.homOfLE (inf_le_right.trans inf_le_left : V ≤ U j)) (c₁ ≫ a j m) :=
    h₁.comp (HA j m) (by simp)
  obtain ⟨c₂, h₂, e₂⟩ := PullsBack.cancel (S.homOfLE (inf_le_left : V ≤ U i ⊓ U j)) h₁' (HB i j) (by simp)
  have h₂' : PullsBack t' (t i) (S.homOfLE (inf_le_left.trans inf_le_left : V ≤ U i)) (c₂ ≫ a i j) :=
    h₂.comp (HA i j) (by simp)
  obtain ⟨c₃, h₃, e₃⟩ := PullsBack.cancel (S.homOfLE hVim) h₂' (HA i m) (by simp)
  have h₃' : PullsBack t' (t m) (S.homOfLE hVm) (c₃ ≫ b i m) := h₃.comp (HB i m) (by simp)
  have hφ : φk = c₃ ≫ b i m := hrig V.toScheme m (S.homOfLE hVm) t' φk (c₃ ≫ b i m) inferInstance hk.1 h₃'.1
    hk.2.1 h₃'.2.1 (fun l => by rw [hk.2.2 l, h₃'.2.2 l])
  have hq : (x ≫ (u i j).A.hom) ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) =
      (y ≫ (u j m).A.hom) ≫ S.homOfLE (inf_le_left : U j ⊓ U m ≤ U j) := by
    rw [Category.assoc, Category.assoc, ← (HB i j).1.1.w, ← (HA j m).1.1.w, ← Category.assoc, hxy, Category.assoc]
  have sq := isPullback_opens_inf_le (X := S) (inf_le_right : U i ⊓ U j ≤ U j) (inf_le_left : U j ⊓ U m ≤ U j)
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : T ⟶ V.toScheme, q ≫ S.homOfLE (inf_le_left : V ≤ U i ⊓ U j) = x ≫ (u i j).A.hom ∧
      q ≫ S.homOfLE (inf_le_right : V ≤ U j ⊓ U m) = y ≫ (u j m).A.hom :=
    ⟨sq.lift _ _ hq, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : T ⟶ t'.A.left, w ≫ c₁ = y ∧ w ≫ t'.A.hom = q :=
    ⟨h₁.1.1.lift y q hq₂.symm, h₁.1.1.lift_fst _ _ _, h₁.1.1.lift_snd _ _ _⟩
  have hwx : w ≫ c₂ = x := by
    apply (HB i j).1.1.hom_ext
    · rw [Category.assoc, e₂, ← Category.assoc, hw₁, hxy]
    · rw [Category.assoc, h₂.1.1.w, ← Category.assoc, hw₂, hq₁]
  have hbase : q ≫ S.homOfLE hVim = z ≫ (u i m).A.hom := by
    have e₅ : ∀ {W : Scheme.{0}} (h : W ⟶ (U i ⊓ U m).toScheme),
        h ≫ (U i ⊓ U m).ι = (h ≫ S.homOfLE (inf_le_left : U i ⊓ U m ≤ U i)) ≫ (U i).ι := fun h => by simp
    rw [← cancel_mono (U i ⊓ U m).ι, Category.assoc, Scheme.homOfLE_ι, e₅ (z ≫ (u i m).A.hom)]
    simp only [Category.assoc]
    rw [← reassoc_of% (HA i m).1.1.w, ← reassoc_of% hxz, reassoc_of% (HA i j).1.1.w, ← reassoc_of% hq₁]
    simp
  have hwz : w ≫ c₃ = z := by
    apply (HA i m).1.1.hom_ext
    · rw [Category.assoc, e₃, ← Category.assoc, hwx, hxz]
    · rw [Category.assoc, h₃.1.1.w, ← Category.assoc, hw₂, hbase]
  calc y ≫ b j m = w ≫ c₁ ≫ b j m := by rw [← Category.assoc, hw₁]
    _ = w ≫ c₃ ≫ b i m := by rw [e₁, hφ]
    _ = z ≫ b i m := by rw [← Category.assoc, hwz]
end GlobalTheory.ThetaCocycle
