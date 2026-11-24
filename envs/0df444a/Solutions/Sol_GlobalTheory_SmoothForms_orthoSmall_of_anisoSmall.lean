-- Prove2me | solution 1 for GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:35.996054+00:00
-- url     : https://prove2.me/submissions/3e2200db-2192-4d0d-b2c3-6201dbe97082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalFrameOfAnisotropicFiniteLengths
import Theorems.Thm_GlobalTheory_SmoothForms_Sized_proj_le
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
open Module Submodule
namespace GlobalTheory.SmoothForms
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (HA : AnisoSmall E) :
    OrthoSmall E := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, 0, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, k₁, hS₁, h0₁, H₁⟩ := HA (n + 1) n.succ_ne_zero N hN
    obtain ⟨M, hM, hMS⟩ := GlobalTheory.HermClass.exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, k₂, hS₂, h0₂, H₂⟩ := ih _ (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, k₁ + (k₁ + 1) * 4 * k₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ ν B hV H
    obtain ⟨v, hv, hvS, hvν⟩ := H₁ V h Λ ν B hV H
    have hs := H.symm
    have hO := H.stable
    have hint := H.int
    have hB1 : 1 ≤ B := by linarith [H.two_le]
    have hBT : B ≤ B ^ (k₁ + 1) := le_self_pow₀ hB1 (Nat.succ_ne_zero _)
    have hT2 : 2 ≤ B ^ (k₁ + 1) := H.two_le.trans hBT
    have hvT : ν v ≤ B ^ (k₁ + 1) := hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_succ _))
    have hproj : ∀ x, ν x ≤ B → ν (h v v • x - h x v • v) ≤ (B ^ (k₁ + 1)) ^ 4 := fun x hx =>
      H.proj_le hT2 hvT (hx.trans hBT)
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    have H' : Sized (h.domRestrict₁₂ W W) Λ' (M * N) (fun w : W => ν w) ((B ^ (k₁ + 1)) ^ 4) :=
      { symm := fun x y => hs x y
        nondeg := fun y hy => Subtype.ext (H.nondeg y fun x => by
          have h1 : h y (p x) = 0 := hy (p x)
          rw [hyp] at h1
          exact (mul_eq_zero.1 h1).resolve_left ha0)
        fg := by
          apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
          exact H.fg.of_le (map_comap_le _ _)
        stable := fun c hc x hx => hO c hc x hx
        int := fun x hx y hy => hint x hx y hy
        dual := fun y hy => by
          have h1 : (N : E) • a • (y : V) ∈ Λ := H.dual _ fun x hx => by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
            exact hy _ (hpΛ x hx)
          have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
          rw [smul_smul, smul_smul] at h2
          rw [hΛ', Submodule.coe_smul]
          convert h2 using 2
          push_cast; field_simp
        two_le := hT2.trans (le_self_pow₀ (by linarith) (by norm_num))
        nonneg := fun x => H.nonneg x
        add_le := fun x y => H.add_le x y
        smul_le := fun c x => H.smul_le c x
        form_le := fun x y => H.form_le x y
        span := by
          rw [eq_top_iff]
          intro w _
          have h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤
              (span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}).comap p :=
            span_le.2 fun x hx => subset_span ⟨hpΛ x hx.1, hproj x hx.2⟩
          have h2 : p w ∈ span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4} := h1 (H.span ▸ mem_top)
          have h3 : w = a⁻¹ • p w := Subtype.ext (by
            have : h w v = 0 := w.2
            simp [hp, this, ha0])
          rw [h3]; exact smul_mem _ _ h2 }
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' _ _ hWr H'
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact ⟨Or.inl hvS, hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_add_right _ _))⟩
      | succ i =>
        refine ⟨Or.inr (huS i).1, (huS i).2.trans ?_⟩
        rw [← pow_mul, ← pow_mul, ← mul_assoc]
        exact pow_le_pow_right₀ hB1 (Nat.le_add_left _ _)
end GlobalTheory.SmoothForms
