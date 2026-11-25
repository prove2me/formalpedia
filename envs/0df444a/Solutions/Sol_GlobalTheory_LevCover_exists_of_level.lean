-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:48.226919+00:00
-- url     : https://prove2.me/submissions/771cb5f9-b6bf-445d-99de-0a4469f397dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Theorems.Thm_GlobalTheory_LevCover_exists_coprime_zpow
import Theorems.Thm_GlobalTheory_LevelTwist_twist_ev
import Theorems.Thm_GlobalTheory_tateIso_ev_eq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LevelTwist.twist_ev



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.LevCover
theorem _root_.solution
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (N : ℕ)
    (hL : ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  classical
  choose b hb using fun a => (I.onto N hN (α a)).1 (hpow a)
  let K : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have memK : ∀ x y, I.ev N x = I.ev N y → x - y ∈ K := by
    intro x y hxy
    obtain ⟨z, hz⟩ := (tateIso_ev_eq_iff I hN x y).1 hxy
    exact LinearMap.mem_range.2
      ⟨z, by rw [hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  let β : D.La →ₗ[𝓞 E] D.La ⧸ K :=
    { toFun := fun a => Submodule.Quotient.mk (b a)
      map_add' := fun a c => by
        rw [← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.add, hb, hb, hadd]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.lin, hb, hlin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property K.mkQ β K.mkQ_surjective
  have hfα : ∀ a, I.ev N (f a) = α a := by
    intro a
    have h1 : (Submodule.Quotient.mk (f a) : D.La ⧸ K) = Submodule.Quotient.mk (b a) :=
      LinearMap.congr_fun hf a
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq K).1 h1)
    rw [← hb a]
    exact (tateIso_ev_eq_iff I hN _ _).2
      ⟨z, by rw [← hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hEF : ∀ a c, (N : ℤ) ∣ D.EF (f a) (f c) - ν * D.EF a c := by
    intro a c
    have h1 := I.isom N hN (f a) (f c)
    rw [hfα, hfα] at h1
    have h2 := he _ _ _ _ (hiso a c) h1
    rw [hξν, ← zpow_mul] at h2
    refine ((I.ζ_prim N hN).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, ← h2, mul_inv_cancel]
  obtain ⟨g, hgf, hgν⟩ := hL f ν hN hνc hEF
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgν
  · rw [LevelTwist.twist_ev, ← hfα a]
    exact LevelTwist.ev_congr I hN (hgf a)
end GlobalTheory.LevCover
