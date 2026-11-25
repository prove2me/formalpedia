-- Prove2me | solution 1 for GlobalTheory.PolyNorm.eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:02.749303+00:00
-- url     : https://prove2.me/submissions/4ac8d66c-7865-4cb6-bc1d-5ee6df5f2fb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
import Theorems.Thm_GlobalTheory_PolyNorm_ev_map
import Theorems.Thm_GlobalTheory_PolyNorm_gen_coeff
import Theorems.Thm_GlobalTheory_PolyNorm_ev_homog
import Theorems.Thm_GlobalTheory_PolyNorm_shift_poly
import Theorems.Thm_GlobalTheory_PolyNorm_mul_all
import Theorems.Thm_GlobalTheory_PolyNorm_ev_one
import Theorems.Thm_GlobalTheory_PolyNorm_exists_ext
import Theorems.Thm_GlobalTheory_PolyNorm_monic_ev
import Theorems.Thm_GlobalTheory_PolyNorm_eq_prod_of_mul
import Theorems.Thm_GlobalTheory_PolyNorm_norm_all
import Theorems.Thm_GlobalTheory_PolyNorm_det_eq_prod
import Theorems.Thm_GlobalTheory_T_eq_of_norm_prod_aeval_eq_moduli


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (N : Polynomial ℤ → ℚ) (Good : Polynomial ℤ → Prop), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous m ∧ ∀ a : Fin r → ℤ, N (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → N 1 = 1 → (∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t)) → (∀ F G, Good F → Good G → N (F * G) = N F * N G) → (∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) → ∀ F, ((N F : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m U N Good hΦ h1 hG hm hn
  choose Φ hh hΦ using hΦ
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    rw [show ∑ i : Fin r, monomial (i : ℕ) (F.coeff i) = F from gen_coeff F hF] at this
    rw [this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have hm' := mul_all N Φ hN Good hG hm
  have hn' := norm_all U N Good (shift_poly N Φ hN) hG hn
  obtain ⟨E, _, _, _, _⟩ : ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E),
      IsAlgClosed E ∧ Algebra.IsAlgebraic ℚ_[l] E :=
    ⟨AlgebraicClosure ℚ_[l], inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have inj : Function.Injective (algebraMap ℚ_[l] E) := (algebraMap ℚ_[l] E).injective
  obtain ⟨M, hM⟩ := exists_ext N Φ hN h1 hm' E
  obtain ⟨hP, hPd⟩ := monic_ev (hh 2) (ev_one N Φ hN h1 1)
  set P := ev (Φ 2) (C X - X : ℚ[X][X]) with hPdef
  let ψ : ℤ_[l] →+* E := (algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom
  let V : Matrix (Fin m) (Fin m) E := U.map ψ
  have roots : ∀ S : E[X], S.Monic → S = (S.roots.map fun x => X - C x).prod := fun S hS =>
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hS IsAlgClosed.card_roots_eq_natDegree).symm
  let a := (P.map (algebraMap ℚ E)).roots
  have ha : P.map (algebraMap ℚ E) = (a.map fun x => X - C x).prod := roots _ (hP.map _)
  have hac : Multiset.card a = m := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = (a.map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M a (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← mul_one (C c), ev_homog (hh 1), ev_one N Φ hN h1, mul_one, hac]
    · have := congrArg (eval β) ha
      rw [eval_multiset_prod, Multiset.map_map, eval_map, ← coe_eval₂RingHom, hPdef,
        ev_map] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  have hNa : ∀ F : ℤ[X], algebraMap ℚ_[l] E (N F : ℚ_[l]) = (a.map fun x => aeval x F).prod := by
    intro F
    have := hMa (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap] at this
    rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le), map_ratCast,
      ← eq_ratCast (algebraMap ℚ E), hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
    congr 2
    all_goals exact RingHom.ext_int _ _
  have hDb : ∀ b : Multiset E, V.charpoly = (b.map fun x => X - C x).prod → ∀ F : ℤ[X],
      algebraMap ℚ_[l] E ((aeval U F).det : ℤ_[l]) = (b.map fun x => aeval x F).prod := by
    intro b hb F
    have := det_eq_prod V b hb (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap, aeval_map_algebraMap] at this
    rw [← this]
    change ψ _ = _
    rw [RingHom.map_det]
    congr 1
    exact (aeval_algHom_apply ψ.mapMatrix.toIntAlgHom U F).symm
  have hPm : (P.map (Rat.castHom ℚ_[l])).map (algebraMap ℚ_[l] E) = P.map (algebraMap ℚ E) := by
    rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_rat _ _
  have hQm : (U.charpoly.map PadicInt.Coe.ringHom).map (algebraMap ℚ_[l] E) = V.charpoly := by
    rw [Polynomial.map_map, ← Matrix.charpoly_map]
  have hb := roots _ V.charpoly_monic
  have key := GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli l E a V.charpoly.roots (P.map (Rat.castHom ℚ_[l]))
    (U.charpoly.map PadicInt.Coe.ringHom) (hPm.trans ha) (hQm.trans hb) (fun F u v hu hv => by
      rw [← hNa] at hu
      rw [← hDb _ hb] at hv
      rw [inj hu, inj hv, hn']
      rfl)
  intro F
  apply inj
  rw [hNa, hDb a]
  rw [← hQm, ← key, hPm, ha]
end GlobalTheory.PolyNorm
