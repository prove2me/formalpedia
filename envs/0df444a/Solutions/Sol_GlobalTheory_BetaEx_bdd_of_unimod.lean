-- Prove2me | solution 1 for GlobalTheory.BetaEx.bdd_of_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:27.148053+00:00
-- url     : https://prove2.me/submissions/59005928-5639-45fe-98f8-8c5afbb268a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_mem_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.BetaEx
theorem _root_.solution [IsCMField E] (Λ : GenLat E n) (h : Λ.Unimod) : Bdd Λ.La := by
  classical
  have hfull : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let u : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
    have hu : ∀ w, ∑ j, IsCMField.complexConj E (u j) * w j = f w := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [u, IsCMField.complexConj_apply_apply, smul_eq_mul, mul_comm]
      congr 2
      ext k; simp [Pi.single_apply, eq_comm]
    have hk : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
    have huL : u ∈ Λ.La := (h u).2 fun w hw => by rw [hu, hk w hw]; exact zero_mem _
    have h0 := hu u
    rw [hk u huL] at h0
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg φ h0
    simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
      ← Complex.normSq_eq_conj_mul_self] at h1
    have h2 : ∑ j, Complex.normSq (φ (u j)) = 0 := by exact_mod_cast h1
    have h3 : ∀ j, u j = 0 := fun j => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)
      simpa using this
    apply hf0
    ext w
    simp [← hu, h3]
  have hmul : ∀ x : Fin n → E, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ Λ.La := by
    intro x
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E
      (Λ.La : Set (Fin n → E)) x (by rw [hfull]; trivial)
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  choose a ha0 ha using fun j : Fin n => hmul (Pi.single j 1)
  have hA : ∀ j, (∏ i, a i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := by
    intro j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul]
    exact Λ.La.smul_mem _ (ha j)
  refine ⟨IsCMField.ringOfIntegersComplexConj E (∏ i, a i), ?_, fun v hv => (mem_std _).2 fun j => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (AlgEquiv.injective _)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => ha0 i
  · obtain ⟨b, hb⟩ := (h _).1 (hA j) v hv
    refine ⟨b, ?_⟩
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at hb
    change _ = ((IsCMField.ringOfIntegersComplexConj E (∏ i, a i) : 𝓞 E) : E) * v j
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    simpa [Algebra.smul_def] using hb
end GlobalTheory.BetaEx
