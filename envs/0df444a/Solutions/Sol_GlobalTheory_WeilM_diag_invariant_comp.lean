-- Prove2me | solution 1 for GlobalTheory.WeilM.diag_invariant_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:11.032903+00:00
-- url     : https://prove2.me/submissions/819534a0-c317-41c0-8f82-aa517ec95e89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_WeilM_invariant_comp_mulVec
import Theorems.Thm_GlobalTheory_WeilM_diag_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_eq_zero_of_mul_invariant
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
namespace GlobalTheory.WeilM
theorem _root_.solution [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by
  classical
  have := SplitWeil.t2Space F
  have := nonarch_field F
  have hlc := isLocallyConstant_addChar ψ hψ

  have hz : ∀ φ ∈ SB (κ ⊕ κ → F), (∀ x, φ (Sum.elim x x) = 0) → l φ = 0 := by
    intro φ hφ h0
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → F => fun u => ψ (u ⬝ᵥ Sum.elim y (-y))) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      rw [← hl 0 y φ hφ]
      congr 1
      funext u
      simp [schr]
    · intro u hu
      obtain ⟨k, hk⟩ : ∃ k, u (Sum.inl k) - u (Sum.inr k) ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hu
        rw [← h0 (u ∘ Sum.inl)]
        congr 1
        ext (k | k)
        · rfl
        · exact (sub_eq_zero.mp (hne k)).symm
      obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ1
      refine ⟨_, ⟨Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))), rfl⟩, ?_⟩
      have : u ⬝ᵥ Sum.elim (Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))))
          (-Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k)))) = a := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr u]
        rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_single, dotProduct_single, ← sub_eq_add_neg,
          ← sub_mul]
        exact mul_div_cancel₀ _ hk
      show ψ _ ≠ 1
      rwa [this]

  let K : Set (κ → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  let e : (κ → F) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → F) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → F) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → F), ext f ∈ SB (κ ⊕ κ → F) := by
    intro f hf
    have c3 : Continuous fun p : (κ → F) × (κ → F) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → F) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → F), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub]
    refine hz _ (sub_mem hφ (hSB _ (diag_mem_SB hφ))) fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → F), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  have h' := diag_mem_SB hφ'
  rw [hres φ hφ, hres φ' hφ']
  simp only [h] at h' ⊢
  exact invariant_comp_mulVec _ hinv g (diag_mem_SB hφ) h'
end GlobalTheory.WeilM
