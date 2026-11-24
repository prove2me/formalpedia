-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.final
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:15.40419+00:00
-- url     : https://prove2.me/submissions/36709d53-47d1-49c2-93bc-4730171bfe1c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_form_isHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_toE_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_mem_UG_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_toE_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_isTor_one
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_isTor_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_exists_unif
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_exists_cover
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_isCartan_of
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution : StDelta → StExists → StFrame → StTor → StDecomp → StIwahori →
    (∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L),
      (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)),
      IsLat L Λ →
      (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J),
        (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧
        (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧
        IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧
        ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧
      ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧
        ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U) → StCartanU := by
  intro hΔ hE hF hT hD hI H L _ _ _ _ s hs hn hne n J hJ hdet U hU
  have hinv : IsInv s := ⟨hs, hn, hne⟩
  obtain ⟨δ, hδ⟩ := hΔ L s hinv
  have hh := form_isHerm s J hs hJ hdet
  obtain ⟨Λ, hΛ⟩ := hE L s hinv δ hδ (Fin n → L) (form s J) hh
  obtain ⟨l, e, f, W, u, -, hfr, had, -⟩ := hF L s hinv δ hδ _ (form s J) hh Λ Λ hΛ hΛ
  obtain ⟨p, hp0, hp1, hpm⟩ := exists_unif L
  obtain ⟨hK, hU'⟩ := H L s hn n J Λ hΛ.1
  obtain ⟨π, hπ0, hπ1, hπU⟩ := hU' U hU
  obtain ⟨K, K₀, hKm, hK₀m, hKo, hKc, hK₀c, -, hnorm⟩ := hK π hπ0 hπ1
  refine ⟨K, fun g hg => hπU g ((hKm g).1 hg), hKo, hKc, ?_⟩
  obtain ⟨d, c, hcK, hcov⟩ := exists_cover K K₀ hKo hK₀c
  have hKc' : ∀ g : UG s J, g ∈ K ↔ IsCong Λ π (toE g.1) := hKm
  have hK₀' : ∀ g : UG s J, g ∈ K₀ ↔ ∀ x, toE g.1 x ∈ Λ ↔ x ∈ Λ := hK₀m
  have hiso : ∀ g : UG s J, IsIso (form s J) (toE g.1) := fun g => (mem_UG_iff s J g.1).1 g.2
  have hinj : ∀ a b : UG s J, toE a.1 = toE b.1 → a = b := fun a b h => Subtype.ext (toE_injective h)
  have hex : ∀ r : Fin l → ℕ, ∃ g : UG s J, IsTor s e f W (fun i => p ^ r i) (toE g.1) ∧
      ∀ t' : (Fin n → L) ≃ₗ[L] (Fin n → L), IsTor s e f W (fun i => p ^ r i) t' → t' = toE g.1 := by
    intro r
    obtain ⟨t, ht, htor, huniq⟩ := hT L s hinv δ hδ _ (form s J) hh l e f W hfr (fun i => p ^ r i)
      (fun i => pow_ne_zero _ hp0)
    obtain ⟨g, rfl⟩ := toE_surj s J t ht
    exact ⟨g, htor, huniq⟩
  choose T hTt hTe using hex
  have hTu : ∀ (r : Fin l → ℕ) (g' : UG s J), IsTor s e f W (fun i => p ^ r i) (toE g'.1) → g' = T r :=
    fun r g' h' => hinj _ _ (hTe r _ h')
  have h0 : T 0 = 1 := by
    refine (hTu 0 1 ?_).symm
    simpa using isTor_one s e f W
  have hadd : ∀ a b, T (a + b) = T a * T b := by
    intro a b
    refine (hTu (a + b) (T a * T b) ?_).symm
    have := isTor_mul (hTt a) (hTt b)
    simpa [pow_add] using this
  refine ⟨d, l, isCartan_of K K₀ T h0 hadd c hcK hcov hnorm ?_ ?_⟩
  · intro g
    obtain ⟨k, t, k', r, hr, hk, hk', hkΛ, hk'Λ, htor, heq⟩ :=
      hD L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ had p hp0 hp1 hpm (toE g.1) (hiso g)
    obtain ⟨k₁, rfl⟩ := toE_surj s J k hk
    obtain ⟨k₂, rfl⟩ := toE_surj s J k' hk'
    obtain rfl := hTe r t htor
    refine ⟨k₁, (hK₀' _).2 hkΛ, k₂, (hK₀' _).2 hk'Λ, r, hr, ?_⟩
    apply hinj
    simpa using heq
  · intro k hk
    obtain ⟨a, b, ha, hb, hab, hall⟩ := hI L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ.1 had π hπ1
      (toE k.1) (hiso k) ((hKc' k).1 hk)
    obtain ⟨a₀, rfl⟩ := toE_surj s J a ha
    obtain ⟨b₀, rfl⟩ := toE_surj s J b hb
    refine ⟨a₀, b₀, hinj _ _ (by simpa using hab), fun r hr => ?_⟩
    have hmono : Monotone fun i => ‖p ^ r i‖ := fun i j hij => by
      simp only [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) hp1.le (hr hij)
    have hone : ∀ i, ‖p ^ r i‖ ≤ 1 := fun i => by
      simp only [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp1.le
    obtain ⟨h1, h2⟩ := hall (fun i => p ^ r i) (toE (T r).1) (fun i => pow_ne_zero _ hp0) hmono hone (hTt r)
    exact ⟨(hKc' _).2 (by simpa using h1), (hKc' _).2 (by simpa using h2)⟩
end GlobalTheory.CompanionTheory.CartanU
