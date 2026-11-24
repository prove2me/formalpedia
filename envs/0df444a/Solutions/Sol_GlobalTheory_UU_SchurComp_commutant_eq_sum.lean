-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.commutant_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:26.778843+00:00
-- url     : https://prove2.me/submissions/1084dade-7d68-4f81-9eb0-fad5b51ccb59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Theorems.Thm_GlobalTheory_linearIndependent_of_comm_smul


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
    [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Fintype K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Fintype.card K * Nat.card H) (P : K → E →ₗ[F] E) (hP0 : ∀ k, P k ≠ 0)
    (hP1 : ∀ k v, P k (P k v) = P k v) (hP2 : ∀ k l v, k ≠ l → P k (P l v) = 0)
    (hPΦ : ∀ k h v, P k (Φ (m h) v) = Φ (m h) (P k v)) (φ : E →ₗ[F] E)
    (hφ : ∀ h v, φ (Φ (m h) v) = Φ (m h) (φ v)) : ∃ c : K → F, ∑ k, c k • P k = φ := by
  classical
  have hApos : 0 < Nat.card A := Nat.card_pos
  haveI : Nontrivial E := by
    rw [← Module.finrank_pos_iff (R := F)]
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim; omega
    · exact h
  obtain ⟨u, hu0⟩ := exists_ne (0 : E)
  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have hsk : ∀ a b, e a b * e b a = 1 := by
    intro a b
    have h1 := hcomm a b u
    rw [hcomm b a u, smul_smul] at h1
    have h2 : Φ a (Φ b u) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 ((one_smul F _).trans h1)
    exact Units.ext h3.symm
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have he1 : ∀ c, e 1 c = 1 := by
      intro c
      have := hel 1 1 c
      rw [mul_one] at this
      exact (mul_eq_left.mp this.symm)
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  let C : Submodule F (E →ₗ[F] E) :=
    Submodule.span F (Set.range fun a : {a : A // ∀ h, e (m h) a = 1} => (Φ a.1 : E →ₗ[F] E))
  have hC : ∀ ψ : E →ₗ[F] E, (∀ h v, ψ (Φ (m h) v) = Φ (m h) (ψ v)) → ψ ∈ C := by
    intro ψ hψ
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
      (hspan ▸ Submodule.mem_top : ψ ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
    rw [← hc]
    refine C.sum_mem fun a _ => ?_
    by_cases ha : ∀ h, e (m h) a = 1
    · exact C.smul_mem _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨h, hh⟩ := not_forall.1 ha
      have h0 : ∑ a, (c a * ((e (m h) a : F) - 1)) • (Φ a : E →ₗ[F] E) = 0 := by
        ext v
        obtain ⟨v, rfl⟩ := (Φ (m h)).surjective v
        have h1 := hψ h v
        rw [← hc] at h1
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, map_smul,
          LinearMap.zero_apply] at h1 ⊢
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, mul_one, h1]
        rw [sub_eq_zero]
        exact Finset.sum_congr rfl fun a _ => by rw [hcomm (m h) a, smul_smul]
      have h2 := Fintype.linearIndependent_iff.1 hli _ h0 a
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rw [h3, zero_smul]; exact C.zero_mem
      · exact absurd (Units.ext (sub_eq_zero.1 h3)) hh

  let S : Subgroup A := Subgroup.closure (Set.range m)
  let χ : A → A →* Fˣ := fun a => MonoidHom.mk' (fun b => e b a) fun b b' => hel b b' a
  have hS : ∀ a : {a : A // ∀ h, e (m h) a = 1}, S ≤ (χ a.1).ker := fun a =>
    (Subgroup.closure_le _).2 (by rintro _ ⟨h, rfl⟩; exact a.2 h)
  let ω : {a : A // ∀ h, e (m h) a = 1} → (A ⧸ S →* F) := fun a =>
    (Units.coeHom F).comp (QuotientGroup.lift S (χ a.1) fun x hx => hS a hx)
  have hω : Function.Injective ω := fun a a' h => Subtype.ext (hinj (funext fun b => by
    have h1 : e b a.1 = e b a'.1 := Units.ext (DFunLike.congr_fun h (QuotientGroup.mk b))
    have h2 := hsk a.1 b
    rw [h1] at h2
    exact congrArg Units.val (mul_right_cancel (h2.trans (hsk a'.1 b).symm))))
  have hcard : Fintype.card {a : A // ∀ h, e (m h) a = 1} ≤ Fintype.card K := by
    have h1 := ((linearIndependent_monoidHom (A ⧸ S) F).comp ω hω).fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card (α := A ⧸ S)] at h1
    have h2 : Nat.card H ≤ Nat.card S := Nat.card_le_card_of_injective
      (fun h => (⟨m h, Subgroup.subset_closure ⟨h, rfl⟩⟩ : S)) fun a b h => hm (congrArg Subtype.val h)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    have h4 : 0 < Nat.card S := Nat.card_pos
    refine h1.trans (Nat.le_of_mul_le_mul_right ?_ h4)
    rw [← h3]
    exact hc.trans (Nat.mul_le_mul_left _ h2)
  have hPli : LinearIndependent F P := by
    refine Fintype.linearIndependent_iff.2 fun c hc k => ?_
    by_contra h0
    refine hP0 k (LinearMap.ext fun v => ?_)
    have h1 := congrArg (P k) (LinearMap.congr_fun hc v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, LinearMap.zero_apply, map_zero] at h1
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hP2 k l v hl.symm, smul_zero]) (by simp), hP1] at h1
    exact (smul_eq_zero.1 h1).resolve_left h0
  have hle : Submodule.span F (Set.range P) ≤ C :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hC _ (hPΦ k))
  have heq : Submodule.span F (Set.range P) = C :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [finrank_span_eq_card hPli]
      exact (finrank_range_le_card _).trans hcard)
  exact (Submodule.mem_span_range_iff_exists_fun F).mp (heq ▸ hC φ hφ)
end GlobalTheory.UU.SchurComp
