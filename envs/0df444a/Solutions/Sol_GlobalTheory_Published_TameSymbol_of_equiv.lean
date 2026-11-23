-- Prove2me | solution 1 for GlobalTheory.Published.TameSymbol.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:40.404433+00:00
-- url     : https://prove2.me/submissions/cb34ea9a-b166-4515-b670-2f2057e76192

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.TameQuot
namespace GlobalTheory.Published
namespace TameSymbol
theorem _root_.solution (hT : TameSymbol) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hq : normV v ≡ 1 [MOD l ^ n]) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (e : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n)) :
    ∃ u : (ZMod (l ^ n))ˣ, ∀ x : Ω, IsUnifRoot v (l ^ n) x →
      ∀ (γ : Dec (F := F) A) (c : ZMod (l ^ n)), (γ : G F Ω) ∈ Ine (F := F) A →
        (γ : G F Ω) x = ζ ^ c.val * x →
        ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
        ∀ (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)),
          (Submodule.Quotient.mk y : H1 (muDec F A l n)) ∈
            H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) →
          c * e (cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y)) =
            u * (z.1 γ * y.1 φ) := by
  obtain ⟨⟨inv, hinv⟩, h⟩ := hT F Ω l n A v hA hl hq ζ hζ
  have key : ∀ (a b : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n)) w,
      a w = a (b.symm 1) * b w := fun a b w => by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one,
      LinearEquiv.symm_apply_apply]
  have hu : e (inv.symm 1) * inv (e.symm 1) = 1 := by
    rw [← key, LinearEquiv.apply_symm_apply]
  refine ⟨-(Units.mkOfMulEqOne _ _ hu), fun x hx γ c hγ hc φ hφ z y hy => ?_⟩
  have h1 := (h x hx γ c hγ hc).2 _ hinv φ hφ z y hy
  rw [LinearEquiv.coe_coe] at h1
  rw [key e inv, mul_left_comm, h1]
  simp
end TameSymbol
end GlobalTheory.Published
