-- Prove2me | solution 1 for GlobalTheory.ResidueDegreeChart.inertiaDeg_eq_finrank_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:37.527688+00:00
-- url     : https://prove2.me/submissions/e15db83c-80b0-4e07-a6e9-226af85af113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ResidueDegreeChart
namespace GlobalTheory.ResidueDegreeChart
theorem _root_.solution {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L
end GlobalTheory.ResidueDegreeChart
