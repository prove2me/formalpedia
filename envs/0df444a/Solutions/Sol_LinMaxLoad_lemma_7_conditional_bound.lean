-- Prove2me | solution 1 for LinMaxLoad.lemma_7_conditional_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:40.27456+00:00
-- url     : https://prove2.me/submissions/44f59c18-a701-49dd-ae03-93e04a733efd

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_expLoad
import Theorems.Thm_LinMaxLoad_lemma_7_load_identity

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.Fibre

open Classical

variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]

/-- restriction of a linear map to a submodule -/
def res (W : Submodule K E) (l : ℕ) (h : E →ₗ[K] (Fin l → K)) : W →ₗ[K] (Fin l → K) :=
  h.comp W.subtype

/-- (a) restriction is surjective -/
theorem res_surjective (W : Submodule K E) (l : ℕ) :
    Function.Surjective (res (K := K) W l) := by
  intro φ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  exact ⟨g, hg⟩

theorem res_sub (W : Submodule K E) (l : ℕ) (h h' : E →ₗ[K] (Fin l → K)) :
    res W l (h - h') = res W l h - res W l h' := by
  ext x i
  simp [res]

theorem res_add (W : Submodule K E) (l : ℕ) (h h' : E →ₗ[K] (Fin l → K)) :
    res W l (h + h') = res W l h + res W l h' := by
  ext x i
  simp [res]

end LinMaxLoad.Dev.Fibre
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace LinMaxLoad.Dev.CondBound

open Classical

theorem card_le_maxLoad {A B : Type*} [DecidableEq B] (h : A → B) (S : Finset A) (b : B) :
    (S.filter fun a => h a = b).card ≤ LinMaxLoad.maxLoad h S := by
  by_cases hb : b ∈ S.image h
  · exact Finset.le_sup (f := fun b => (S.filter fun a => h a = b).card) hb
  · have : (S.filter fun a => h a = b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hab
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    rw [this]; simp

/-- coarsening can only increase the max load -/
theorem maxLoad_le_comp {A B C : Type*} [DecidableEq B] [DecidableEq C] (f : A → B) (π : B → C)
    (S : Finset A) : LinMaxLoad.maxLoad f S ≤ LinMaxLoad.maxLoad (fun a => π (f a)) S := by
  unfold LinMaxLoad.maxLoad
  refine Finset.sup_le fun b _ => ?_
  calc (S.filter fun a => f a = b).card
      ≤ (S.filter fun a => π (f a) = π b).card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter] at ha ⊢
        exact ⟨ha.1, by rw [ha.2]⟩
    _ ≤ _ := card_le_maxLoad (fun a => π (f a)) S (π b)

/-- uniform pushforward under a surjective additive hom -/
theorem sum_pushforward {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (c : B) (F : B → ℝ) :
    (∑ k, F (c + π k)) / (Fintype.card A : ℝ) = (∑ b, F b) / (Fintype.card B : ℝ) := by
  set m : ℕ := (Finset.univ.filter fun k : A => π k = 0).card with hm
  have hfib : ∀ b : B, (Finset.univ.filter fun k : A => π k = b).card = m := by
    intro b
    obtain ⟨a, ha⟩ := hπ b
    rw [hm]
    refine Finset.card_bij (fun k _ => k - a) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_sub] at hk ⊢
      rw [hk, ha, sub_self]
    · intro k _ k' _ h
      simpa using h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨k + a, ?_, by simp⟩
      simp [map_add, hk, ha]
  have hmpos : 0 < m := by
    obtain ⟨a, ha⟩ := hπ 0
    rw [hm]
    exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩
  have hcard : Fintype.card A = ∑ b : B, m := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun b _ => hfib b
  have hs : ∑ k, F (c + π k) = ∑ b : B, (m : ℝ) * F (c + b) := by
    rw [← Finset.sum_fiberwise (Finset.univ) (fun k : A => π k) (fun k => F (c + π k))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F (c + b))
      (fun k hk => by simp only [Finset.mem_filter] at hk; rw [hk.2])]
    rw [Finset.sum_const, hfib b]; simp
  have hs2 : ∑ b : B, F (c + b) = ∑ b : B, F b :=
    Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun _ => rfl)
  rw [hs, ← Finset.mul_sum, hs2, hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  have : (0 : ℝ) < m := by exact_mod_cast hmpos
  have : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  field_simp

/-- a surjection `K^ℓ → K^(ℓ-d)` killing a subspace of dimension at most `d`. -/
theorem exists_psi {K : Type*} [Field K] [Fintype K] (ℓ d : ℕ) (hd : d ≤ ℓ)
    (H : Submodule K (Fin ℓ → K)) (hH : Module.finrank K H ≤ d) :
    ∃ ψ : (Fin ℓ → K) →ₗ[K] (Fin (ℓ - d) → K), Function.Surjective ψ ∧ H ≤ LinearMap.ker ψ := by
  have hQ := Submodule.finrank_quotient_add_finrank H
  rw [Module.finrank_fin_fun] at hQ
  set n := Module.finrank K ((Fin ℓ → K) ⧸ H) with hn
  have hle : ℓ - d ≤ n := by omega
  let e := (Module.finBasis K ((Fin ℓ → K) ⧸ H)).equivFun
  let proj : (Fin n → K) →ₗ[K] (Fin (ℓ - d) → K) := LinearMap.funLeft K K (Fin.castLE hle)
  have hproj : Function.Surjective proj :=
    LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hle)
  refine ⟨proj ∘ₗ e.toLinearMap ∘ₗ H.mkQ, ?_, ?_⟩
  · exact hproj.comp (e.surjective.comp H.mkQ_surjective)
  · intro x hx
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero H).2 hx]

end LinMaxLoad.Dev.CondBound

namespace LinMaxLoad

open Classical in
open LinMaxLoad.Dev.CondBound in
theorem chk_lemma_7_conditional_bound {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) (hV : Module.finrank K V ≤ ℓ)
    (T : Finset E) (φ : V →ₗ[K] (Fin ℓ → K)) :
    condAvgLin K E ℓ (fun h => h.comp V.subtype = φ)
        (fun h => (maxLoad (h : E → Fin ℓ → K) (cosetSum V T) : ℝ)) ≤
      (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) *
        expLoad K (E ⧸ V) (ℓ - Module.finrank K V) (T.image V.mkQ) := by
  letI : Fintype (E →ₗ[K] (Fin ℓ → K)) := Fintype.ofFinite _
  letI : Fintype ((E ⧸ V) →ₗ[K] (Fin ℓ → K)) := Fintype.ofFinite _
  letI : Fintype ((E ⧸ V) →ₗ[K] (Fin (ℓ - Module.finrank K V) → K)) := Fintype.ofFinite _
  set d := Module.finrank K V with hd
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi (K := K) ℓ d hV (LinearMap.range φ)
    (by simpa [hd] using LinearMap.finrank_range_le φ)
  obtain ⟨h0, hh0⟩ := Dev.Fibre.res_surjective (K := K) V ℓ φ
  -- the extensions
  let hk : ((E ⧸ V) →ₗ[K] (Fin ℓ → K)) → (E →ₗ[K] (Fin ℓ → K)) := fun k => h0 + k.comp V.mkQ
  have hres : ∀ k, (hk k).comp V.subtype = φ := by
    intro k
    have : Dev.Fibre.res V ℓ (hk k) = φ := by
      rw [Dev.Fibre.res_add, hh0]
      have : Dev.Fibre.res V ℓ (k.comp V.mkQ) = 0 := by
        ext x i; simp [Dev.Fibre.res, (Submodule.Quotient.mk_eq_zero V).2 x.2]
      rw [this, add_zero]
    exact this
  have hsumfib : ∀ f : (E →ₗ[K] (Fin ℓ → K)) → ℝ,
      ∑ h ∈ Finset.univ.filter (fun h : E →ₗ[K] (Fin ℓ → K) => h.comp V.subtype = φ), f h =
        ∑ k, f (hk k) := by
    intro f
    symm
    refine Finset.sum_bij (fun k _ => hk k) ?_ ?_ ?_ ?_
    · intro k _; simp [hres k]
    · intro k _ k' _ hkk
      have : k.comp V.mkQ = k'.comp V.mkQ := by simpa [hk] using hkk
      exact (LinearMap.cancel_right V.mkQ_surjective).1 this
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
      have hz : Dev.Fibre.res V ℓ (h - h0) = 0 := by
        rw [Dev.Fibre.res_sub, hh0]; exact sub_eq_zero.2 hh
      have hle : V ≤ LinearMap.ker (h - h0) := by
        intro x hx
        have := LinearMap.congr_fun hz ⟨x, hx⟩
        simpa [Dev.Fibre.res] using this
      refine ⟨V.liftQ (h - h0) hle, Finset.mem_univ _, ?_⟩
      ext x : 1
      simp [hk]
    · intro k _; rfl
  have hv0 : ∀ v : V, ψ (φ v) = 0 := fun v => hψk ⟨v, rfl⟩
  have hker0 : V ≤ LinearMap.ker (ψ ∘ₗ h0) := by
    intro x hx
    have := LinearMap.congr_fun hh0 ⟨x, hx⟩
    have h2 : h0 x = φ ⟨x, hx⟩ := by simpa [Dev.Fibre.res] using this
    simp [LinearMap.mem_ker, h2, hv0 ⟨x, hx⟩]
  let c0 : (E ⧸ V) →ₗ[K] (Fin (ℓ - d) → K) := V.liftQ (ψ ∘ₗ h0) hker0
  let π : ((E ⧸ V) →ₗ[K] (Fin ℓ → K)) →+ ((E ⧸ V) →ₗ[K] (Fin (ℓ - d) → K)) :=
    { toFun := fun k => ψ ∘ₗ k
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hπ : Function.Surjective π := by
    intro k'
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective ψ
      (LinearMap.range_eq_top.2 hψs)
    refine ⟨σ ∘ₗ k', ?_⟩
    show ψ ∘ₗ (σ ∘ₗ k') = k'
    rw [← LinearMap.comp_assoc, hσ]; rfl
  have key : ∀ k, (maxLoad (hk k : E → Fin ℓ → K) (cosetSum V T) : ℝ) ≤
      (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) *
        (maxLoad (⇑(c0 + π k) : E ⧸ V → Fin (ℓ - d) → K) (T.image V.mkQ) : ℝ) := by
    intro k
    have hid := lemma_7_load_identity ℓ V T (hk k)
    have hdr : (hk k).domRestrict V = φ := hres k
    have e : Module.finrank K (LinearMap.ker ((hk k).domRestrict V)) =
        Module.finrank K (LinearMap.ker φ) := by rw [hdr]
    rw [e] at hid
    have hle : V.map (hk k) ≤ LinearMap.ker ψ := by
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have := LinearMap.congr_fun (hres k) ⟨x, hx⟩
      have h2 : hk k x = φ ⟨x, hx⟩ := by simpa using this
      simp [LinearMap.mem_ker, h2, hv0 ⟨x, hx⟩]
    have hco := maxLoad_le_comp
      (Submodule.mapQ V (V.map (hk k)) (hk k) (Submodule.le_comap_map (hk k) V) :
        E ⧸ V → (Fin ℓ → K) ⧸ V.map (hk k))
      ((V.map (hk k)).liftQ ψ hle) (T.image V.mkQ)
    have hfun : (fun a => (V.map (hk k)).liftQ ψ hle
        (Submodule.mapQ V (V.map (hk k)) (hk k) (Submodule.le_comap_map (hk k) V) a)) =
        (⇑(c0 + π k) : E ⧸ V → Fin (ℓ - d) → K) := by
      funext x
      induction x using Submodule.Quotient.induction_on with
      | H e =>
        simp [c0, π, hk]
    rw [hfun] at hco
    have : (maxLoad (hk k : E → Fin ℓ → K) (cosetSum V T)) ≤
        Fintype.card K ^ Module.finrank K (LinearMap.ker φ) *
          maxLoad (⇑(c0 + π k) : E ⧸ V → Fin (ℓ - d) → K) (T.image V.mkQ) := by
      rw [hid]; exact Nat.mul_le_mul_left _ hco
    exact_mod_cast this
  have hA : (Fintype.card ((E ⧸ V) →ₗ[K] (Fin ℓ → K)) : ℝ) > 0 := by
    exact_mod_cast Fintype.card_pos
  have hcardf : ((Finset.univ.filter
      (fun h : E →ₗ[K] (Fin ℓ → K) => h.comp V.subtype = φ)).card : ℝ) =
      (Fintype.card ((E ⧸ V) →ₗ[K] (Fin ℓ → K)) : ℝ) := by
    have := hsumfib (fun _ => 1)
    simpa using this
  unfold condAvgLin expLoad avgLin
  rw [hcardf, hsumfib]
  rw [div_le_iff₀ hA]
  have hpf := sum_pushforward π hπ c0
    (fun b => (maxLoad (⇑b : E ⧸ V → Fin (ℓ - d) → K) (T.image V.mkQ) : ℝ))
  calc ∑ k, (maxLoad (hk k : E → Fin ℓ → K) (cosetSum V T) : ℝ)
      ≤ ∑ k, (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) *
        (maxLoad (⇑(c0 + π k) : E ⧸ V → Fin (ℓ - d) → K) (T.image V.mkQ) : ℝ) :=
        Finset.sum_le_sum fun k _ => key k
    _ = (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker φ) *
        ∑ k, (maxLoad (⇑(c0 + π k) : E ⧸ V → Fin (ℓ - d) → K) (T.image V.mkQ) : ℝ) := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [div_eq_iff hA.ne'] at hpf
        rw [hpf]
        field_simp
        convert mul_comm _ _

end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_lemma_7_conditional_bound := @LinMaxLoad.chk_lemma_7_conditional_bound
