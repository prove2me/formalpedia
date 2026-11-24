-- Prove2me | solution 1 for GlobalTheory.SignGen.signs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:42.641784+00:00
-- url     : https://prove2.me/submissions/0496c31b-6bf3-4e42-ba4f-bd15ab8c142c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Theorems.Thm_GlobalTheory_SignGen_cm_restrict_inj
import Theorems.Thm_GlobalTheory_SignGen_round_signs
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.SignGen
namespace GlobalTheory.SignGen
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (c : I → ℝ) :
    ∃ a : OF E, ∀ i, |c i| ≤ c i * (φ i (algebraMap (OF E) E a)).re := by
  classical
  have hφinj : Function.Injective φ := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    exact (hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm
  haveI : Finite I := Finite.of_injective φ hφinj
  haveI : Fintype I := Fintype.ofFinite I
  let χ : I → (OF E) →* ℂ := fun i => (φ i).toMonoidHom.comp (algebraMap (OF E) E).toMonoidHom
  have hχ : ∀ i a, χ i a = φ i (algebraMap (OF E) E a) := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    intro i j hij
    exact cm_restrict_inj E I φ hφ i j (fun a => by rw [← hχ, ← hχ, hij])
  have hli : LinearIndependent ℂ (fun i => (χ i : OF E → ℂ)) :=
    (linearIndependent_monoidHom (OF E) ℂ).comp χ hχinj
  have hreal : ∀ i (a : OF E), ((φ i (algebraMap (OF E) E a)).re : ℂ) = φ i (algebraMap (OF E) E a) := by
    intro i a
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) (algebraMap (OF E) E a)
    have h2 : IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
      IsCMField.complexConj_apply_eq_self (K := E) (a : maximalRealSubfield E)
    rw [h2] at h1
    exact Complex.conj_eq_iff_re.1 h1.symm
  let Φ : OF E →+ (I → ℝ) :=
    { toFun := fun a i => (φ i (algebraMap (OF E) E a)).re
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hΦ : ∀ a i, Φ a i = (φ i (algebraMap (OF E) E a)).re := fun _ _ => rfl
  have hspan : Submodule.span ℝ ((Φ.range : AddSubgroup (I → ℝ)) : Set (I → ℝ)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    let b : I → (I → ℝ) := fun i j => if i = j then 1 else 0
    have hsum : ∀ a : OF E, ∑ i, f (b i) * (φ i (algebraMap (OF E) E a)).re = 0 := by
      intro a
      have hmem : Φ a ∈ Submodule.span ℝ ((Φ.range : AddSubgroup (I → ℝ)) : Set (I → ℝ)) :=
        Submodule.subset_span ⟨a, rfl⟩
      have h1 := hfle hmem
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ f] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hΦ, smul_eq_mul, mul_comm]
    have hz := Fintype.linearIndependent_iff.1 hli (fun i => ((f (b i) : ℝ) : ℂ)) (by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hχ]
      have : ∑ i, ((f (b i) : ℝ) : ℂ) * φ i (algebraMap (OF E) E a)
          = ((∑ i, f (b i) * (φ i (algebraMap (OF E) E a)).re : ℝ) : ℂ) := by
        push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hreal])
      rw [this, hsum a, Complex.ofReal_zero])
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f, LinearMap.zero_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := hz i
    simp only [Complex.ofReal_eq_zero] at this
    simp [b, this]
  obtain ⟨g, ⟨a, rfl⟩, hg⟩ := round_signs I Φ.range hspan c
  exact ⟨a, fun i => hg i⟩
end GlobalTheory.SignGen
