-- Prove2me | solution 1 for GlobalTheory.BorelAlg.Equivariant.isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:28.227445+00:00
-- url     : https://prove2.me/submissions/76402326-1ff0-4f88-9d5b-330f01793edc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_GlobalTheory_BorelAlg_coeff_scale
import Theorems.Thm_GlobalTheory_BorelAlg_gen_det_ne_zero
import Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_numer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]
namespace GlobalTheory.BorelAlg
namespace Equivariant
theorem _root_.solution {a : ι × ℕ → ℕ} {Q : MvPolynomial (Lt m) L}
    (hf : Equivariant m L S a (algebraMap _ S Q)) :
    Q.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
  let T := FractionRing (Polynomial (MvPolynomial (Lt m) L))
  let g : Polynomial (MvPolynomial (Lt m) L) →+* T := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0 := fun hq h => hq (hg (h.trans (map_zero _).symm))
  let g' : MvPolynomial (Lt m) L →+* T := g.comp Polynomial.C
  let t : T := g Polynomial.X
  have ht : t ≠ 0 := hg0 Polynomial.X_ne_zero
  let x := fun τ => g'.mapMatrix (gen m L τ)
  have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => by
    rw [← RingHom.map_det]
    exact hg0 (Polynomial.C_ne_zero.2 (gen_det_ne_zero m L τ))
  have key := hf.numer (N := 0) (P := Q) (by simp) (g'.comp C) x (fun τ => t • x τ)
    (fun τ => t • 1) hx
    (fun τ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ ht) (hx τ))
    (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) (fun τ => by simp)
  have e1 : eval₂Hom (g'.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) = g' := by
    ext <;> simp [x, gen]
  have e2 : eval₂Hom (g'.comp C) (fun p : Lt m => (t • x p.1) p.2.1 p.2.2) =
      g.comp (eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i))) := by
    ext
    · simp [g']
    · simp [x, gen, g', t]; ring
  rw [e1, e2] at key
  simp only [pow_zero, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Finset.prod_pow_eq_pow_sum] at key
  have k2 : eval₂Hom ((Polynomial.C : MvPolynomial (Lt m) L →+* _).comp C)
        (fun i => Polynomial.X * Polynomial.C (X i)) Q =
      Polynomial.C Q * Polynomial.X ^ (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
    apply hg
    rw [map_mul, map_pow, mul_comm]
    exact key
  have k3 := coeff_scale Q (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ)))
  rw [k2, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at k3
  rw [k3]
  exact homogeneousComponent_isHomogeneous _ _
end Equivariant
end GlobalTheory.BorelAlg
