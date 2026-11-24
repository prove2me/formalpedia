-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.proportional_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:00:12.176544+00:00
-- url     : https://prove2.me/submissions/f31ef2eb-0496-47aa-9503-40e14f8d6a3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Theorems.Thm_GlobalTheory_UU_SchurComp_commutant_eq_sum
import Theorems.Thm_GlobalTheory_UU_SchurComp_finrank_le_of_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {F : Type} [Field F] {A : Type} [CommGroup A] [Finite A] {E : Type} [AddCommGroup E]
    [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [AddCommGroup Q] [Module F Q] (cl : X → K) (ex : X → E →ₗ[F] Q)
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ex β v ∈ Submodule.span F (Set.range b))
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α : X) (hα : ∃ v, ex α v ≠ 0) (f₁ f₂ : E →ₗ[F] Q) (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, f₁ v ∈ Submodule.span F (Set.range b))
    (hb₂ : ∀ v, f₂ v ∈ Submodule.span F (Set.range b))
    (hint : ∀ h v v', f₂ v = f₁ v' → f₂ (Φ (m h) v) = f₁ (Φ (m h) v')) : ∃ a : F, ∀ v, f₂ v = a • f₁ v := by
  classical
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)] at hc hn
  have hApos : 0 < Nat.card A := Nat.card_pos
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim; omega
    · exact h)
  have hext : ∀ v v', (∀ β, ex β v = ex β v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hinj _ fun β => by rw [map_sub, h, sub_self])
  choose p hp using hP
  have hp' : ∀ k v β, ex β (p k v) = if cl β = k then ex β v else 0 := fun k v β => by
    split_ifs with h
    exacts [(hp k v β).1 h, (hp k v β).2 h]
  let P : K → E →ₗ[F] E := fun k =>
    { toFun := p k
      map_add' := fun v v' => hext _ _ fun β => by
        rw [map_add, hp', hp', hp']; split_ifs <;> simp
      map_smul' := fun c v => hext _ _ fun β => by
        rw [map_smul, hp', hp']; split_ifs <;> simp }
  have hP : ∀ k v β, ex β (P k v) = if cl β = k then ex β v else 0 := hp'
  have hP0 : ∀ k, P k ≠ 0 := fun k h => by
    obtain ⟨β, hβ, v, hv⟩ := hne k
    have := hP k v β
    rw [h, if_pos hβ] at this
    exact hv (this.symm.trans (map_zero _))
  have hP1 : ∀ k v, P k (P k v) = P k v := fun k v => hext _ _ fun β => by
    rw [hP, hP]; split_ifs <;> rfl
  have hP2 : ∀ k l v, k ≠ l → P k (P l v) = 0 := fun k l v hkl => hinj _ fun β => by
    rw [hP, hP]; split_ifs with h h'
    exacts [absurd (h.symm.trans h') hkl, rfl, rfl]
  have hPΦ : ∀ k h v, P k (Φ (m h) v) = Φ (m h) (P k v) := fun k h v => hext _ _ fun β => by
    rw [hP]
    split_ifs with hβ
    · have := hΦ h β (v - P k v) (by rw [map_sub, hP, if_pos hβ, sub_self])
      rwa [map_sub, map_sub, sub_eq_zero] at this
    · exact (hΦ h β _ (by rw [hP, if_neg hβ])).symm
  have hW : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v ∈ LinearMap.range (P (cl β)), ex β v = 0 → v = 0 := by
    rintro β hβ _ ⟨v, rfl⟩
    exact h3 β hβ _ fun γ hγ => by rw [hP, if_neg hγ]
  have hle : ∀ k, Module.finrank F (LinearMap.range (P k)) ≤ n := fun k => by
    obtain ⟨β, rfl, hβ⟩ := hne k
    obtain ⟨b, hb⟩ := hb β
    exact (finrank_le_of_inj _ _ (hW β hβ) b hb).1
  have hge : n ≤ Module.finrank F (LinearMap.range (P (cl α))) := by
    have hi : Function.Injective (LinearMap.pi fun k => (P k).rangeRestrict) :=
      (injective_iff_map_eq_zero _).2 fun v hv => hinj _ fun β => by
        have h1 : P (cl β) v = 0 := congrArg Subtype.val (congrFun hv (cl β))
        have h2 := hP (cl β) v β
        rw [h1, if_pos rfl] at h2
        exact h2.symm.trans (map_zero _)
    have h1 := LinearMap.finrank_le_finrank_of_injective hi
    rw [Module.finrank_pi_fintype] at h1
    by_contra hlt
    have h2 : ∑ k, Module.finrank F (LinearMap.range (P k)) < ∑ _k : K, n :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨cl α, Finset.mem_univ _, not_le.1 hlt⟩
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
    omega
  have hW₁ : ∀ v ∈ LinearMap.range (P (cl α)), f₁ v = 0 → v = 0 := fun v hv h => hW α hα v hv ((hk v).1 h)
  have hext₁ : ∀ v ∈ LinearMap.range (P (cl α)), ∀ v' ∈ LinearMap.range (P (cl α)), f₁ v = f₁ v' → v = v' :=
    fun v hv v' hv' h => sub_eq_zero.1 (hW₁ _ (sub_mem hv hv') (by rw [map_sub, h, sub_self]))
  choose q hq hq' using fun v => (finrank_le_of_inj _ f₁ hW₁ b hb₁).2 hge _ (hb₂ v)
  let φ : E →ₗ[F] E :=
    { toFun := q
      map_add' := fun v v' => hext₁ _ (hq _) _ (add_mem (hq _) (hq _)) (by rw [map_add, hq', hq', hq', map_add])
      map_smul' := fun c v => hext₁ _ (hq _) _ (Submodule.smul_mem _ _ (hq _)) (by
        rw [map_smul, hq', hq', map_smul]; rfl) }
  obtain ⟨c, hc⟩ := commutant_eq_sum e Φ hdim hmul hcomm hnd m hm hc P hP0 hP1 hP2 hPΦ φ fun h v =>
    hext₁ _ (hq _) _ (by
      obtain ⟨x, hx⟩ := hq v
      exact ⟨Φ (m h) x, (hPΦ _ _ _).trans (congrArg _ hx)⟩) ((hq' _).trans (hint h v (q v) (hq' v).symm))
  refine ⟨c (cl α), fun v => ?_⟩
  rw [← hq' v]
  show f₁ (φ v) = _
  rw [← hc, LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl α) (fun l _ hl => by
    rw [LinearMap.smul_apply, map_smul, (hk _).2 (by rw [hP, if_neg hl.symm]), smul_zero]) (by simp),
    LinearMap.smul_apply, map_smul]
  congr 1
  have := (hk (P (cl α) v - v)).2 (by rw [map_sub, hP, if_pos rfl, sub_self])
  rwa [map_sub, sub_eq_zero] at this
end GlobalTheory.UU.SchurComp
