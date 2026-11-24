-- Prove2me | solution 1 for GlobalTheory.TorusConst.exists_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:07.704009+00:00
-- url     : https://prove2.me/submissions/ac3e2247-18d1-4e9a-a352-6bb8dd0ca689

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.TorusConst
theorem _root_.solution {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    (F : sp K R[X] ⟶ B) (V : B.left.Opens) (e : R →ₐ[K] L) (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ a : R[X], a.map (e : R →+* L) = 1 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A) (x : A) (q),
      (val F c x).left q ∉ V → eval₂ (c : R →+* A) x a = 0 := by
  let Z : Set (PrimeSpectrum R[X]) := F.left ⁻¹' (V : Set B.left)ᶜ
  have hZ : IsClosed Z := V.2.isClosed_compl.preimage F.left.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  let φ : R[X] →+* L[X] := (aevalTower (CAlgHom.comp e) (X : L[X])).toRingHom
  have hφ : φ = mapRingHom (e : R →+* L) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ]
    · simp [φ]
  have htop : I.map φ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : PrimeSpectrum.comap φ ⟨m, hm.isPrime⟩ ∈ Z := by
      rw [hI]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact h1 (hF ⟨m, hm.isPrime⟩)
  have hs : Function.Surjective φ := by
    rw [hφ]
    exact Polynomial.map_surjective _ he
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective φ hs).1 (htop ▸ Submodule.mem_top : (1 : L[X]) ∈ I.map φ)
  refine ⟨a, by rw [← ha1, hφ]; rfl, fun A _ _ c x (q : PrimeSpectrum A) hq => ?_⟩
  have h1 : PrimeSpectrum.comap (aevalTower c x).toRingHom q ∈ Z := hq
  rw [hI] at h1
  have h2 : aevalTower c x a ∈ q.asIdeal := h1 ha
  rw [Ideal.eq_bot_of_prime q.asIdeal] at h2
  exact h2
end GlobalTheory.TorusConst
