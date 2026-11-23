-- Prove2me | solution 1 for GlobalTheory.HolChart.derivation_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:05.072149+00:00
-- url     : https://prove2.me/submissions/df2b00d4-3413-47d5-bffa-4b09d1c165c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.HolChart
namespace GlobalTheory.HolChart
theorem _root_.solution {g : ℕ} {A : Type} [CommRing A] (φ : MvPolynomial (Fin g) ℂ →+* A)
    (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ) (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have h1 : D 1 = 0 := by simpa using h0 1
  have hP : ∀ p, D (φ p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hm, hp, hX]; simp
  let F : A →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun f f' => by ext <;> simp [hm, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun f f' => by ext <;> simp }
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ p, F (φ p) = F₀ (φ p) := fun p => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ :=
    { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ := { F₀ with commutes' := fun p => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this
end GlobalTheory.HolChart
