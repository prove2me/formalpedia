-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.sum_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:18.965855+00:00
-- url     : https://prove2.me/submissions/f55ba30c-c06d-4e82-a29b-907b4047f1c8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_continuous_algHom
import Theorems.Thm_GlobalTheory_LocalTraceSum_norm_lt_one
import Theorems.Thm_GlobalTheory_LocalTraceSum_mem_ker
import Theorems.Thm_GlobalTheory_LocalTraceSum_ker_isPrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_norm_le_one
import Theorems.Thm_GlobalTheory_LocalTraceSum_norm_l_lt
import Theorems.Thm_GlobalTheory_LocalTraceSum_exists_ext
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ p, p ∈ S ↔ (l : 𝓞 F) ∈ p.asIdeal) → ∀ (K : S → Type) [∀ p, Field (K p)] [∀ p, Algebra ℚ_[l] (K p)] [∀ p, FiniteDimensional ℚ_[l] (K p)] [∀ p, ValuativeRel (K p)] [∀ p, TopologicalSpace (K p)] (ι : ∀ p, F →+* K p), (∀ p, IsNonarchimedeanLocalField (K p)) → (∀ p, Continuous (algebraMap ℚ_[l] (K p))) → (∀ p, DenseRange (ι p)) → (∀ p (x y : F), (ι p x ≤ᵥ ι p y) ↔ p.1.valuation F x ≤ p.1.valuation F y) → ∀ a : F, ∑ p, Algebra.trace ℚ_[l] (K p) (ι p a) = ((Algebra.trace ℚ F a : ℚ) : ℚ_[l]) := by
  intro F _ _ l _ S hS K _ _ _ _ _ ι hK hc hι hv a
  classical
  let Ω := PadicAlgCl l
  have hv' : ∀ p (x : F), valuation (K p) (ι p x) < 1 ↔ p.1.valuation F x < 1 := by
    intro p x
    rw [← not_le, ← not_le, not_iff_not, ← map_one (valuation (K p)), ← map_one (ι p),
      ← Valuation.Compatible.vle_iff_le (v := valuation (K p)), hv, map_one]
  have hch : ∀ p, CharZero (K p) := fun p =>
    charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  have hker : ∀ (p : S) (τ : K p →ₐ[ℚ_[l]] Ω), p.1.asIdeal = ker (τ.toRingHom.comp (ι p)) := by
    intro p τ
    refine p.1.isMaximal.eq_of_le (ker_isPrime _).ne_top fun x hx => ?_
    rw [mem_ker]
    exact norm_lt_one (hc p) τ ((hv' p x).2 ((p.1.valuation_lt_one_iff_mem x).2 hx))
  let e : (Σ p : S, (K p →ₐ[ℚ_[l]] Ω)) → (F →ₐ[ℚ] Ω) := fun t =>
    (t.2.toRingHom.comp (ι t.1)).toRatAlgHom
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨p, τ⟩ ⟨q, τ'⟩ h
      have h1 : τ.toRingHom.comp (ι p) = τ'.toRingHom.comp (ι q) :=
        RingHom.ext fun x => DFunLike.congr_fun h x
      have hpq : p = q := by
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        rw [hker p τ, hker q τ', h1]
      subst hpq
      congr 1
      apply DFunLike.coe_injective
      exact (hι p).equalizer (continuous_algHom (hc p) τ) (continuous_algHom (hc p) τ')
        (funext fun x => DFunLike.congr_fun h1 x)
    · intro σ
      have hl : (l : 𝓞 F) ∈ ker σ.toRingHom := by
        rw [mem_ker]
        simpa using norm_l_lt (l := l) (Ω := Ω)
      let p : HeightOneSpectrum (𝓞 F) := ⟨ker σ.toRingHom, ker_isPrime _, fun h => by
        rw [h, Ideal.mem_bot] at hl
        exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)⟩
      have hp : p ∈ S := (hS p).2 hl
      obtain ⟨τ, hτ⟩ := exists_ext (hc ⟨p, hp⟩) (ι ⟨p, hp⟩) (hι _) σ.toRingHom
        (fun x hx => norm_le_one _ p rfl ((hv' ⟨p, hp⟩ x).1 hx).le)
      exact ⟨⟨⟨p, hp⟩, τ⟩, AlgHom.ext hτ⟩
  apply (algebraMap ℚ_[l] Ω).injective
  rw [map_sum, map_ratCast]
  have h1 := trace_eq_sum_embeddings (K := ℚ) Ω (x := a)
  rw [eq_ratCast] at h1
  rw [h1, ← he.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_eq_sum_embeddings Ω]
  rfl
end GlobalTheory.LocalTraceSum
