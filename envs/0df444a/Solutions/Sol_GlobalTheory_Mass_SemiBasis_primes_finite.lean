-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.primes_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:30.858943+00:00
-- url     : https://prove2.me/submissions/2732297b-352d-4b99-a98d-9ddfc0298d91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) : {P : Ideal (A K hd) | P.IsPrime}.Finite := by
  have hd0 : (d : 𝓞 K) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (d : 𝓞 K) ∈ P}.Finite := by
    have h0 : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hd0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hdP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hd0 (by simpa using hdP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hdP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap (𝓞 K) (A K hd)))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo (d : 𝓞 K)) (A K hd) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A K hd)), ?_,
    IsLocalization.map_under (primeTo (d : 𝓞 K)) (A K hd) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A K hd))
  have hsub : (Q : Set (𝓞 K)) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal (𝓞 K))), ((id i : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    refine Set.disjoint_left.mp hdisj (?_ : x ∈ primeTo (d : 𝓞 K)) hx
    intro I hI hdI hxI
    apply hn
    simp only [Set.mem_iUnion]
    exact ⟨I, by simpa using ⟨hI, hdI⟩, hxI⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i.IsMaximal ∧ (d : 𝓞 K) ∈ i := by simpa using hi
    exact this.1.isPrime)).1 hsub
  have hI' : I.IsMaximal ∧ (d : 𝓞 K) ∈ I := by simpa using hI
  have : Q = I := hmax.eq_of_le hI'.1.ne_top hle
  right
  rw [this]
  exact hI'
end GlobalTheory.Mass.SemiBasis
