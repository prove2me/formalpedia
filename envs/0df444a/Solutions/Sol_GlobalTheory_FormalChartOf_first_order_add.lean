-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.first_order_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:47.839742+00:00
-- url     : https://prove2.me/submissions/4c61191f-7a11-4abb-b53c-683d59ecc299

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
import Theorems.Thm_GlobalTheory_FormalChartOf_tsze_nil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G))
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
    (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
include h0 hnat hinj hsurj
namespace GlobalTheory.FormalChartOf
theorem _root_.solution (a b : Fin g → R₀) :
    x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k)) *
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (b k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (a k + b k)) := by
  let T := TrivSqZeroExt R₀ (R₀ × R₀)
  let a' : Fin g → T := fun k => TrivSqZeroExt.inr (a k, 0)
  let b' : Fin g → T := fun k => TrivSqZeroExt.inr (0, b k)
  have ha' : ∀ k, IsNilpotent (a' k) := fun k => tsze_nil _ rfl
  have hb' : ∀ k, IsNilpotent (b' k) := fun k => tsze_nil _ rfl
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (φ : T →ₐ[R₀] S),
      spMap φ ≫ (x T a' * x T b') = x S (fun k => φ (a' k)) * x S (fun k => φ (b' k)) := by
    intro S _ _ φ
    rw [MonObj.comp_mul, hnat _ _ φ a' ha', hnat _ _ φ b' hb']
  obtain ⟨c, hc, hxc⟩ := hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (R₀ × R₀))
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun u hu => tsze_nil u hu) (x T a' * x T b') (by
      rw [key]
      change x R₀ 0 * x R₀ 0 = 1
      rw [h0, _root_.mul_one])
  have hc0 : ∀ k, (c k).fst = 0 := hc
  have hcn : ∀ k, IsNilpotent (c k) := fun k => tsze_nil _ (hc0 k)
  have key2 : ∀ f : (R₀ × R₀) →ₗ[R₀] R₀,
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (a k, 0))) *
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (0, b k))) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (f (c k).snd)) := by
    intro f
    have h := key (DualNumber R₀) (TrivSqZeroExt.map f)
    rw [hxc, hnat _ _ _ c hcn] at h
    have e1 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (a' k)) =
        fun k => TrivSqZeroExt.inr (f (a k, 0)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e2 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (b' k)) =
        fun k => TrivSqZeroExt.inr (f (0, b k)) := funext fun k => TrivSqZeroExt.map_inr _ _
    have e3 : (fun k => (TrivSqZeroExt.map f : T →ₐ[R₀] DualNumber R₀) (c k)) =
        fun k => TrivSqZeroExt.inr (f (c k).snd) := funext fun k => by
      ext
      · rw [TrivSqZeroExt.fst_map, hc0]; rfl
      · rw [TrivSqZeroExt.snd_map]; rfl
    rw [e1, e2, e3] at h
    exact h.symm
  have hz : x (DualNumber R₀) (fun _ => TrivSqZeroExt.inr (0 : R₀)) = 1 := h0 _
  have k1 := key2 (LinearMap.fst R₀ R₀ R₀)
  have k2 := key2 (LinearMap.snd R₀ R₀ R₀)
  have k3 := key2 (LinearMap.fst R₀ R₀ R₀ + LinearMap.snd R₀ R₀ R₀)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at k1 k2 k3
  rw [hz, _root_.mul_one] at k1
  rw [hz, _root_.one_mul] at k2
  have j1 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k1
  have j2 := hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) k2
  rw [k3]
  congr 1
  funext k
  rw [TrivSqZeroExt.inr_injective (congrFun j1 k), TrivSqZeroExt.inr_injective (congrFun j2 k)]
end GlobalTheory.FormalChartOf
