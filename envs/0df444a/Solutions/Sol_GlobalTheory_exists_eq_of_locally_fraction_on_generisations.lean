-- Prove2me | solution 1 for GlobalTheory.exists_eq_of_locally_fraction_on_generisations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:23.417551+00:00
-- url     : https://prove2.me/submissions/5a9e60b4-69fe-4e4b-80fb-13c5734dabb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEqOfLocallyFractionOnGenerisations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (K : Type) [Field K] (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra K R]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (R →ₐ[K] k) → k)
    (hW : ∀ (q : Ideal R) [q.IsPrime], ∃ a : Localization.AtPrime q,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : Localization.AtPrime q →ₐ[K] k),
        W k (φ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q))) = φ a) :
    ∃ r : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
      W k φ = φ r := by
  classical
  have h1 : ∀ (q : Ideal R) [q.IsPrime], ∃ g ∉ q, ∃ a : R,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
        RingHom.ker φ ≤ q → φ g * W k φ = φ a := by
    intro q _
    obtain ⟨b, hb⟩ := hW q
    obtain ⟨⟨a, g⟩, hg⟩ := IsLocalization.surj q.primeCompl b
    refine ⟨g, g.2, a, fun k _ _ _ φ hφ => ?_⟩
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := fun y =>
      IsUnit.mk0 _ fun h => y.2 (hφ h)
    let ψ : Localization.AtPrime q →ₐ[K] k := IsLocalization.liftAlgHom (M := q.primeCompl) hu
    have hψ : ∀ x : R, ψ (algebraMap R _ x) = φ x := fun x => by
      simp [ψ, IsLocalization.liftAlgHom_apply]
    have hc : ψ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q)) = φ := by
      ext x; simpa using hψ x
    have h2 := hb k ψ
    rw [hc] at h2
    have h3 := congrArg ψ hg
    simp only [map_mul, hψ] at h3
    rw [h2, mul_comm]; exact h3
  let I : Ideal R :=
    { carrier := {g | ∃ a : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k]
        (φ : R →ₐ[K] k), RingHom.ker φ ∈ minimalPrimes R → φ g * W k φ = φ a}
      zero_mem' := ⟨0, fun k _ _ _ φ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', fun k _ _ _ φ h => by
          rw [map_add, map_add, add_mul, ha k φ h, ha' k φ h]⟩
      smul_mem' := by
        rintro c g ⟨a, ha⟩
        exact ⟨c * a, fun k _ _ _ φ h => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, ha k φ h]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    haveI := hq.isPrime
    obtain ⟨g, hg, a, ha⟩ := h1 q
    have hfin := minimalPrimes.finite_of_isNoetherianRing R
    let S : Finset (Ideal R) := hfin.toFinset.filter fun m => ¬ m ≤ q
    have hS : ¬ S.inf id ≤ q := by
      rw [Ideal.IsPrime.inf_le' inferInstance]
      rintro ⟨m, hm, hmq⟩
      exact (Finset.mem_filter.1 hm).2 hmq
    obtain ⟨h, hh, hhq⟩ := Set.not_subset.1 hS
    have hmem : h * g ∈ I := by
      refine ⟨h * a, fun k _ _ _ φ hφ => ?_⟩
      by_cases hle : RingHom.ker φ ≤ q
      · rw [map_mul, map_mul, mul_assoc, ha k φ hle]
      · have hm : RingHom.ker φ ∈ S := Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hφ, hle⟩
        have h0 : φ h = 0 := (Finset.inf_le (f := id) hm : S.inf id ≤ RingHom.ker φ) hh
        simp [h0]
    rcases hq.isPrime.mem_or_mem (hIq hmem) with h' | h'
    · exact hhq h'
    · exact hg h'
  obtain ⟨r, hr⟩ : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨r, fun k _ _ _ φ => ?_⟩
  haveI hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨g, hg, a, ha⟩ := h1 (RingHom.ker φ)
  obtain ⟨m, hm, hmq⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R))
    (J := RingHom.ker φ) bot_le
  haveI : m.IsPrime := hm.1.1
  let k' := AlgebraicClosure (FractionRing (R ⧸ m))
  let ψ : R →ₐ[K] k' := (IsScalarTower.toAlgHom K (R ⧸ m) k').comp (Ideal.Quotient.mkₐ K m)
  have hinj : Function.Injective (algebraMap (R ⧸ m) k') := by
    rw [IsScalarTower.algebraMap_eq (R ⧸ m) (FractionRing (R ⧸ m)) k']
    exact (algebraMap (FractionRing (R ⧸ m)) k').injective.comp (IsFractionRing.injective _ _)
  have hker : RingHom.ker ψ = m := by
    ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ hinj]
    rfl
  have e1 := hr k' ψ (by rw [hker]; exact hm)
  have e2 := ha k' ψ (by rw [hker]; exact hmq)
  have e3 : g * r - a ∈ m := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, ← e1, ← e2, map_one, one_mul, sub_self]
  have e4 : φ (g * r - a) = 0 := hmq e3
  have e5 := ha k φ le_rfl
  rw [map_sub, map_mul, ← e5, sub_eq_zero] at e4
  exact (mul_left_cancel₀ hg e4).symm
end GlobalTheory
