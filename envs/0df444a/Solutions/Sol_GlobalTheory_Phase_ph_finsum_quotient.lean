-- Prove2me | solution 1 for GlobalTheory.Phase.ph_finsum_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:46.143431+00:00
-- url     : https://prove2.me/submissions/2eeef9b4-1340-4a45-9cf0-30f113d3f39d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
import Theorems.Thm_GlobalTheory_Phase_IsMu_mul
import Theorems.Thm_GlobalTheory_Phase_IsMu_norm_eq_one
import Theorems.Thm_GlobalTheory_Phase_Ph_mul
import Theorems.Thm_GlobalTheory_Phase_ph_zero
import Theorems.Thm_GlobalTheory_T_isZeroOrPosMulRootOfUnity_finite_gaussSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
namespace GlobalTheory.Phase
private theorem quotient_out_sub_mem' {G : Type} [AddCommGroup G] (N : AddSubgroup G) (x : G) :
    (x : G ⧸ N).out - x ∈ N := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm
  rwa [neg_add_eq_sub] at h
end GlobalTheory.Phase
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase
open Classical
namespace GlobalTheory.Phase
theorem _root_.solution {A : Type} [AddCommGroup A] (P S : AddSubgroup A) (φ f : A → ℂ) (c : ℂ) (a : A)
    (hper : ∀ x, ∀ y ∈ P, φ (x + y) = φ x)
    (hfin : (Function.support fun q : A ⧸ P => φ q.out).Finite)
    (hc : Ph c) (hf : Quad S f) (hφ : ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0) :
    Ph (∑ᶠ q : A ⧸ P, φ q.out) := by
  by_cases hc0 : c = 0
  · have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]
    simp only [h0, finsum_zero]
    exact ph_zero

  have hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s := by
    intro s hs t htS htP
    have h1 := hφ (a + (s + t))
    have h2 := hφ (a + s)
    rw [add_sub_cancel_left, if_pos (S.add_mem hs htS)] at h1
    rw [add_sub_cancel_left, if_pos hs] at h2
    have h3 : φ (a + (s + t)) = φ (a + s) := by rw [← add_assoc]; exact hper _ t htP
    exact mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))

  let ψ : S →+ A ⧸ P := (QuotientAddGroup.mk' P).comp S.subtype
  have hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P := fun u => by
    simp [ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  let ι' : S ⧸ ψ.ker →+ A ⧸ P := QuotientAddGroup.kerLift ψ
  have hι : Function.Injective ι' := QuotientAddGroup.kerLift_injective ψ
  let j : S ⧸ ψ.ker → A ⧸ P := fun m => (a : A ⧸ P) + ι' m
  have hj : Function.Injective j := fun m m' h => hι (add_left_cancel h)
  have hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P) := fun u => by
    simp [j, ι', ψ]
  let fb : S ⧸ ψ.ker → ℂ := fun m => f (m.out : A)
  have hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u := by
    intro u
    have hk := (hker _).mp (quotient_out_sub_mem' ψ.ker u)
    have e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A) := by simp
    show f (((u : S ⧸ ψ.ker).out : S) : A) = f u
    rw [e]
    exact hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk
  have hval : ∀ m, φ (j m).out = c * fb m := by
    intro m
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective m
    rw [hjmk, hfb]
    have hk := quotient_out_sub_mem' P (a + (u : A))
    have e : ((a + (u : A) : A) : A ⧸ P).out =
        (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u)) := by abel
    rw [e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]
  have hfbne : ∀ m, fb m ≠ 0 := fun m h => by
    have h1 := (hf.1 _ (m.out).2).norm_eq_one
    simp [fb] at h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out) := by
    rintro _ ⟨m, rfl⟩
    rw [Function.mem_support, hval]
    exact mul_ne_zero hc0 (hfbne m)
  have : Finite (S ⧸ ψ.ker) := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out)))
      (fun m m' h => hj (congrArg Subtype.val h))
  haveI := Fintype.ofFinite (S ⧸ ψ.ker)

  have hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j := by
    intro q hq
    rw [Function.mem_support, hφ] at hq
    split_ifs at hq with hmem
    · refine ⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩
      rw [hjmk]
      simp
    · exact absurd rfl hq
  have hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j)
        (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hval m
  rw [hsum]
  refine Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h0 : fb 0 = f 0 := by simpa using hfb 0
  have e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker) := fun x y => rfl
  rw [e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]
  simp only [hfb]
  simpa using hf.2 _ u.2 _ v.2 _ w.2
end GlobalTheory.Phase
