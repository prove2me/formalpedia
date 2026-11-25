-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:21:58.358384+00:00
-- url     : https://prove2.me/submissions/50f67ee6-4816-4098-9c1e-5045a6426d11

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
import Theorems.Thm_GlobalTheory_FormalChartOf_tsze_nil
import Theorems.Thm_GlobalTheory_FormalChartOf_tmul_eps_surj
import Theorems.Thm_GlobalTheory_FormalChartOf_tmul_eps_eq_zero
import Theorems.Thm_GlobalTheory_FormalChartOf_first_order_add
import Theorems.Thm_GlobalTheory_FormalChartOf_e_zero

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
variable [IsLocalRing R₀] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G))
  (he : ∀ R, Function.Bijective (e R)) (hadd : ∀ R x y, e R (x + y) = e R x * e R y)
  (hen : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
include h0 hnat hinj hsurj he hadd hen
namespace GlobalTheory.FormalChartOf
theorem _root_.solution : ∃ gb : Module.Basis (Fin g) R₀ B.gg, ∀ w : B.gg,
    e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (gb.repr w k)) := by
  have hex : ∀ w : B.gg, ∃ t : Fin g → R₀,
      e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
        x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) := by
    intro w
    obtain ⟨c, hc, hxc⟩ := hsurj (DualNumber R₀) R₀ (dualProj R₀).1 dualProj_sqZero.1
      (fun u hu => tsze_nil u hu) (e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀))) (by
        refine (hen (dualProj R₀) _).symm.trans ?_
        rw [(B.tg_ker _ dualProj_sqZero _).2 ⟨_, rfl⟩]
        exact e_zero B e hadd _)
    have hc0 : ∀ k, (c k).fst = 0 := hc
    refine ⟨fun k => (c k).snd, hxc.trans ?_⟩
    congr 1
    funext k
    ext <;> simp [hc0]
  choose θ hθ using hex
  have huniq : ∀ s t : Fin g → R₀, x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (s k)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)) → s = t := fun s t h =>
    funext fun k => TrivSqZeroExt.inr_injective
      (congrFun (hinj _ _ _ (fun k => tsze_nil _ rfl) (fun k => tsze_nil _ rfl) h) k)
  have hθadd : ∀ v w, θ (v + w) = θ v + θ w := by
    intro v w
    apply huniq
    rw [← hθ, TensorProduct.add_tmul, map_add, hadd, hθ, hθ, first_order_add x h0 hnat hinj hsurj]
    rfl
  have hθsmul : ∀ (r : R₀) w, θ (r • w) = r • θ w := by
    intro r w
    apply huniq
    have hi : (r • DualNumber.eps : DualNumber R₀) * (r • DualNumber.eps) = 0 := by
      rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]
    let f : LHom (dualL R₀) (dualL R₀) := dualToL (dualL R₀)
      ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h⟩ (r • DualNumber.eps) hi
    have hfa : ∀ a : DualNumber R₀, f.1 a = algebraMap R₀ _ a.fst + a.snd • r • DualNumber.eps :=
      fun a => dualTo_apply _ hi a
    have hf : ∀ a ∈ (dualProj R₀).ker, f.1.toLinearMap a ∈ (dualProj R₀).ker := by
      intro a ha
      have ha' : TrivSqZeroExt.fst a = 0 := ha
      change TrivSqZeroExt.fst (f.1 a) = 0
      rw [hfa, ha']
      simp
    have h := B.tg_nat _ _ dualProj_sqZero dualProj_sqZero f hf (w ⊗ₜ epsK R₀)
    have h2 : f.1.toLinearMap.restrict hf (epsK R₀) = r • epsK R₀ := by
      apply Subtype.ext
      change f.1 DualNumber.eps = r • DualNumber.eps
      rw [hfa]
      simp
    rw [LinearMap.lTensor_tmul, h2, ← TensorProduct.smul_tmul] at h
    rw [← hθ, h, hen, hθ]
    refine (hnat _ _ f.1 _ (fun k => tsze_nil _ rfl)).trans ?_
    congr 1
    funext k
    rw [hfa]
    ext <;> simp [mul_comm]
  let L : B.gg →ₗ[R₀] (Fin g → R₀) := ⟨⟨θ, hθadd⟩, hθsmul⟩
  have hL : Function.Bijective L := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      have hw' : θ w = 0 := hw
      have h := hθ w
      rw [hw'] at h
      have h1 : e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) = e (dualL R₀) 0 := by
        rw [h, e_zero B e hadd]
        exact h0 (DualNumber R₀)
      have h2 := (he _).1 h1
      rw [← map_zero (B.tg (dualProj R₀) dualProj_sqZero)] at h2
      exact tmul_eps_eq_zero w (B.tg_inj _ _ h2)
    · intro t
      obtain ⟨y, hy⟩ := (he (dualL R₀)).2 (x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (t k)))
      have hy0 : B.map (dualProj R₀) y = 0 := by
        apply (he _).1
        rw [hen, hy, e_zero B e hadd]
        exact (hnat _ _ (dualProj R₀).1 _ (fun k => tsze_nil _ rfl)).trans (h0 R₀)
      obtain ⟨v, hv⟩ := (B.tg_ker _ dualProj_sqZero y).1 hy0
      obtain ⟨w, rfl⟩ := tmul_eps_surj v
      have h3 : θ w = t := huniq (θ w) t (by rw [← hθ, hv, hy])
      exact ⟨w, h3⟩
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL), fun w => ?_⟩
  have h4 : ∀ k, (Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL)).repr w k = θ w k := fun k => by
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  simp only [h4]
  exact hθ w
end GlobalTheory.FormalChartOf
