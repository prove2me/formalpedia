-- Prove2me | solution 1 for GlobalTheory.LevelCover.levelMap_finite_etale_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:44.959054+00:00
-- url     : https://prove2.me/submissions/78868428-c57c-4067-9515-e2a57283adc0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
import Theorems.Thm_GlobalTheory_LevelCover_spMap_inclusion_self
import Theorems.Thm_GlobalTheory_LevelCover_baseOf_rho
import Theorems.Thm_GlobalTheory_LevelCover_baseOf_zeta
import Theorems.Thm_GlobalTheory_LevelCover_levelMap_over_field

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
theorem _root_.solution : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂
    : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m
    : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫
    s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta
    a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA
    a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro hSm hPull hC _ hRig hRep hCov E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m ⟨_, _, hm₁, hm₂⟩ c c₂ hc rF h₁ h₂
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  obtain rfl : F = F₂ := hc
  exact levelMap_over_field hSm hPull hC hRig hRep hCov Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    _ _ rfl rfl rfl rfl (baseOf_rho _ _ _ _ _) (baseOf_zeta _ _ _ _ _ hd.2.2) rF h₁
    (h₂.trans ((congrArg _ (spMap_inclusion_self _)).trans (Category.comp_id _)))
end GlobalTheory.LevelCover
