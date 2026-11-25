-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.similitude_acts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:36.660408+00:00
-- url     : https://prove2.me/submissions/5b78e5b6-2be0-42fb-aa0c-b6466d46bd52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_inv_sabMap
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_comp_sabMap
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_map_nsmul_of_add
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_mem_of_modN
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_eta_congr
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_etaA_congr
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_twists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_comp_eq_id_of_twists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_modN_tower
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_sec_ext
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_lowerBase_zeta
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_lowerBase_rho

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
noncomputable section
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : Sim D), 1 ≤ D.p + D.q → (l.A : ℤ) ∣ g.ν l.A - 1 → ∃ (o' : Obj D l b s) (m : SABMap o'.t o.t (𝟙 S)), (∀ a, (o'.eta a).left ≫ m.φ = (o.eta (g.f l.M a)).left) ∧ ∀ a, (o'.etaA a).left ≫ m.φ = (o.etaA (g.f l.A a)).left) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r := by
  intro hsm hcomp hlow hrep hsim halg E _ _ _ H D l l₂ Xo Xo₂ hpq hl r jK m ⟨hj, hr, hE, hEA⟩ g ⟨hν, hgM, hgA⟩
  have hred : IsReduced Xo₂.X := by
    haveI := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM₂ : 0 < l₂.M := lt_of_lt_of_le (by norm_num) l₂.three_le
  obtain ⟨i, hi⟩ := (hcomp E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ Xo₂.univ Xo₂.univ Xo₂.univ).1
  obtain ⟨g', hg'⟩ := (halg E H D hpq).2.2.2 g
  have hν' : (l₂.A : ℤ) ∣ g'.ν l₂.A - 1 := by
    have h₁ := (hg' l₂.A l₂.A_pos).2
    have : g'.ν l₂.A - 1 = (g.ν l₂.A * g'.ν l₂.A - 1) - (g.ν l₂.A - 1) * g'.ν l₂.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g' hpq hν'
  obtain ⟨f, hf⟩ := exists_twists Xo₂ g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := exists_twists Xo₂ g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  refine ⟨⟨f, f', comp_eq_id_of_twists Xo₂ hred i hf hf' (fun a => ((hg' _ hM₂).1 a).2)
      (fun a => ((hg' _ l₂.A_pos).1 a).2),
    comp_eq_id_of_twists Xo₂ hred i hf' hf (fun a => ((hg' _ hM₂).1 a).1)
      (fun a => ((hg' _ l₂.A_pos).1 a).1)⟩, hf, ?_⟩
  show f ≫ r = r
  obtain ⟨hfs, ν, e₁, e₂⟩ := hf
  have hζ := lowerBase_zeta jK hl.2.2 hj
  obtain ⟨o, k, c₁, c₂⟩ := hlow E H D l l₂ _ (lowerBase jK) (baseKA l₂) _ _ Xo₂.univ hl rfl hζ
  obtain ⟨id₀, hid₀⟩ := (hcomp E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o o).1
  obtain ⟨k', hk'⟩ := exists_inv_sabMap k id₀.toSABMap hid₀
  have d₁ : ∀ a, (o.eta a).left ≫ k'.φ = (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    rw [← (c₁ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  have d₂ : ∀ a, (o.etaA a).left ≫ k'.φ = (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left := fun a => by
    rw [← (c₂ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  obtain ⟨n, hn⟩ := exists_comp_sabMap k' m (Category.id_comp r)
  obtain ⟨n₀, hn₀⟩ := exists_comp_sabMap k' ν (Category.id_comp f)
  obtain ⟨n', hn'⟩ := exists_comp_sabMap n₀ m rfl
  have t₁ : ∀ a, Xo₂.univ.eta a ^ (l₂.M / l.M) = Xo₂.univ.eta (g.f l₂.M ((l₂.M / l.M) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.eta_add]
    apply sec_ext m
    rw [hE, hE, eta_congr Xo.univ (mem_of_modN l (modN_tower g hM₂ hl.1 a)), eta_congr Xo.univ (hgM a)]
  have t₂ : ∀ a, Xo₂.univ.etaA a ^ (l₂.A / l.A) = Xo₂.univ.etaA (g.f l₂.A ((l₂.A / l.A) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.etaA_add]
    apply sec_ext m
    rw [hEA, hEA, etaA_congr Xo.univ (modN_tower g l₂.A_pos hl.2.2 a), etaA_congr Xo.univ (hgA a)]
  refine (hrep E H D l Xo _ (lowerBase jK) jK _ _ o hred (lowerBase_rho jK hj) rfl).unique
    ⟨by rw [Category.assoc, hr, ← Category.assoc, hfs], ⟨⟨n', fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨hr, ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₁, t₁, e₁, map_nsmul_of_add Xo₂.univ.eta_add,
      Category.assoc, hE, Category.assoc]
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₂, t₂, e₂, map_nsmul_of_add Xo₂.univ.etaA_add,
      Category.assoc, hEA, Category.assoc]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₁, hE]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₂, hEA]
end GlobalTheory.Moduli.LevelAction
