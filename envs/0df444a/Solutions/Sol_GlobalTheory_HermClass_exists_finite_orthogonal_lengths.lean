-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_finite_orthogonal_lengths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:27:20.352798+00:00
-- url     : https://prove2.me/submissions/10989305-d28e-4619-b896-0ef9fdb32201

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_lengths
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HermClass
theorem _root_.solution (n : ℕ) : ∀ {N : ℤ}, N ≠ 0 →
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        ∀ i, h (v i) (v i) ∈ S := by
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, hS₁, h0₁, H₁⟩ := exists_finite_lengths (E := E) (n + 1) n.succ_ne_zero hN
    obtain ⟨M, hM, hMS⟩ := exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, hS₂, h0₂, H₂⟩ := ih (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
    obtain ⟨v, hv, hvS⟩ := H₁ V h Λ hV hs hnd hfg hsp hO hint hdual
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
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' hWr (fun x y => hs x y)
      (fun y hy => Subtype.ext (hnd y fun x => by
        have h1 : h y (p x) = 0 := hy (p x)
        rw [hyp] at h1
        exact (mul_eq_zero.1 h1).resolve_left ha0))
      (by
        apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
        exact hfg.of_le (map_comap_le _ _))
      (by
        rw [eq_top_iff]
        intro w _
        have h1 : span E (Λ : Set V) ≤ (span E (Λ' : Set W)).comap p :=
          span_le.2 fun x hx => subset_span (hpΛ x hx)
        have h2 : p w ∈ span E (Λ' : Set W) := h1 (hsp ▸ mem_top)
        have h3 : w = a⁻¹ • p w := Subtype.ext (by
          have : h w v = 0 := w.2
          simp [hp, this, ha0])
        rw [h3]; exact smul_mem _ _ h2)
      (fun c hc x hx => hO c hc x hx) (fun x hx y hy => hint x hx y hy)
      (fun y hy => by
        have h1 : (N : E) • a • (y : V) ∈ Λ := hdual _ fun x hx => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
          exact hy _ (hpΛ x hx)
        have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
        rw [smul_smul, smul_smul] at h2
        rw [hΛ', Submodule.coe_smul]
        convert h2 using 2
        push_cast; field_simp)
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
      | zero => exact Or.inl hvS
      | succ i => exact Or.inr (huS i)
end GlobalTheory.HermClass
