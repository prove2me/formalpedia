-- Prove2me | solution 1 for GlobalTheory.LevelCover.levelMap_over_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:19.627642+00:00
-- url     : https://prove2.me/submissions/a795d973-53ff-4529-8b25-9b5ed43f4c0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
import Theorems.Thm_GlobalTheory_LevelCover_sab_comp
import Theorems.Thm_GlobalTheory_LevelCover_sab_cancel
import Theorems.Thm_GlobalTheory_LevelCover_sec_cancel
import Theorems.Thm_GlobalTheory_LevelCover_sec_pow
import Theorems.Thm_P2M_GlobalTheory_LevelCover_spMap_id__a96cf4ec904c
import Theorems.Thm_GlobalTheory_LevelCover_represents_pullback
import Theorems.Thm_GlobalTheory_LevelCover_iso_cover

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
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l l₂ : Level H}
namespace GlobalTheory.LevelCover
theorem _root_.solution
    (hSm : ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X)
    (hPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f))
    (hC : ObjCompSt)
    (hRig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (hRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    (hCov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  obtain ⟨o, ⟨mo⟩⟩ := hPull E H D l _ _ (baseKA l) b j _ _ Xo.s
    (pullback.snd Xo.s (spMap j)) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨mo₂⟩⟩ := hPull E H D l₂ _ _ (baseKA l₂) b₂ j₂ _ _ Xo₂.s
    (rF ≫ pullback.snd Xo.s (spMap j)) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  obtain ⟨Y, π, oc, mc, hfin, het, hsur, hmc, univ⟩ := hCov E H D l l₂ _ b b₂ _ _ o hpq hd hρ hζ
  obtain ⟨o₁, ⟨n⟩⟩ := hPull E H D l _ _ b b (RingHom.id _) _ _ _
    (π ≫ pullback.snd Xo.s (spMap j)) π rfl rfl (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨x, hx⟩ := sab_comp mo₂.toSABMap m h₁.symm
  obtain ⟨mF, hmF⟩ := sab_cancel mo.toSABMap x rF rfl
  have := Xo.smooth
  have := Xo₂.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth Xo₂.s := SmoothOfRelativeDimension.smooth D.dim _
  have rY : IsReduced Y := (hSm F Y (π ≫ pullback.snd Xo.s (spMap j)) inferInstance).1
  have rX₂ := (hSm F _ (pullback.snd Xo₂.s (spMap j₂)) inferInstance).1
  obtain ⟨h, hiso, hh⟩ := iso_cover hC (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n mF mc
    ⟨fun a => sec_cancel mF mo.toSABMap _ _ (by
      rw [hmF, hx, ← Category.assoc, sec_pow mo₂.toSABMap _ _ (mo₂.eta a), Category.assoc, hm₁, ← Category.assoc, ← h₁,
        Category.assoc]
      exact congrArg _ (mo.eta a).symm),
    fun a => sec_cancel mF mo.toSABMap _ _ (by
      rw [hmF, hx, ← Category.assoc, sec_pow mo₂.toSABMap _ _ (mo₂.etaA a), Category.assoc, hm₂, ← Category.assoc, ← h₁,
        Category.assoc]
      exact congrArg _ (mo.etaA a).symm)⟩ hmc
    (represents_pullback hC Xo _ (fun S s o hS => hRep E H D l Xo _ b _ S s o hS e₁ e₂) rfl o mo)
    (represents_pullback hC Xo₂ _ (fun S s o hS => hRep E H D l₂ Xo₂ _ b₂ _ S s o hS e₃ e₄) h₂ o₂ mo₂)
    rX₂ rY (hRig E H D l _ _ b b _ _ _ _ o o₁ π (Or.inl rY)) univ
  rw [← hh]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.LevelCover
