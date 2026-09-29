-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_odd_isAdmissibleTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/48a8eacf-0f1e-5df8-837d-5f4de25b3a99

import Mathlib
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
import Theorems.Thm_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_odd_isAdmissibleTwist

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse NumberField.AdelicLevel NumberField.AdelicVolume AdelicDock AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace LTOddTwist

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (padicPlace p) = p := by
  show (Rat.HeightOneSpectrum.primesEquiv (padicPlace p) : ℕ) = p
  rw [padicPlace, Equiv.apply_symm_apply]

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

theorem eq_padicPlace_of_natCast_mem {q : ℕ} [hq : Fact q.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : v = padicPlace q := by
  have h3 : Rat.HeightOneSpectrum.natGenerator v = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hq.out).mp
      ((natCast_mem_asIdeal_iff v q).mp hv)
  unfold padicPlace
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext h3

theorem idealMultiplicity_ratLevel_pow_eq_zero {q : ℕ} [hq : Fact q.Prime] (b : ℕ)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace q) :
    HeckeCharacter.idealMultiplicity ℚ v (ratLevel (q ^ b)) = 0 := by
  classical
  unfold HeckeCharacter.idealMultiplicity
  by_contra hne
  have hdvd : v.asIdeal ∣ ratLevel (q ^ b) :=
    (Associates.count_ne_zero_iff_dvd (ratLevel_ne_bot (pow_ne_zero b hq.out.ne_zero)) v.irreducible).mp hne
  rw [Ideal.dvd_iff_le] at hdvd
  have hmem : ((q ^ b : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hdvd (by unfold ratLevel; exact Ideal.mem_span_singleton_self _)
  rw [Nat.cast_pow] at hmem
  exact hv (eq_padicPlace_of_natCast_mem (v.isPrime.mem_of_pow_mem b hmem))

def chi0 : (ZMod (2 ^ 2))ˣ →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ : ℤ →* ℂ)).comp (MulChar.toUnitHom ZMod.χ₄)

theorem chi0_neg_one : chi0 (-1) = -1 := by
  refine Units.ext ?_
  show ((ZMod.χ₄ ((-1 : (ZMod 4)ˣ) : ZMod 4) : ℤ) : ℂ) = ((-1 : ℂˣ) : ℂ)
  have h : ZMod.χ₄ ((-1 : (ZMod 4)ˣ) : ZMod 4) = -1 := by decide
  rw [h]; simp

theorem far_mul_apply (x y : FiniteAdeleRing (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (x * y) v = x v * y v := rfl

theorem far_neg_apply (x : FiniteAdeleRing (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (-x) v = -(x v) := rfl

theorem far_one_apply (v : HeightOneSpectrum (𝓞 ℚ)) : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl

theorem iar_mul_apply (x y : InfiniteAdeleRing ℚ) (w : InfinitePlace ℚ) : (x * y) w = x w * y w := rfl
theorem iar_neg_apply (x : InfiniteAdeleRing ℚ) (w : InfinitePlace ℚ) : (-x) w = -(x w) := rfl
theorem iar_one_apply (w : InfinitePlace ℚ) : (1 : InfiniteAdeleRing ℚ) w = 1 := rfl

theorem adele_fst_mul (x y : AdeleRing (𝓞 ℚ) ℚ) : (x * y).1 = x.1 * y.1 := rfl
theorem adele_snd_mul (x y : AdeleRing (𝓞 ℚ) ℚ) : (x * y).2 = x.2 * y.2 := rfl
theorem adele_fst_neg (x : AdeleRing (𝓞 ℚ) ℚ) : (-x).1 = -x.1 := rfl
theorem adele_snd_neg (x : AdeleRing (𝓞 ℚ) ℚ) : (-x).2 = -x.2 := rfl
theorem adele_fst_one : (1 : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl
theorem adele_snd_one : (1 : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := rfl

theorem main : ∃ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ ∧
      ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 1 := by
  obtain ⟨η, hfo, hmod, hunit, -, hu, -⟩ :=
    HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv 2 2 chi0
  refine ⟨η, ⟨hfo.isIdeleClassChar, hfo.continuous, hunit⟩, fun w hw => ?_⟩

  set v₂ : HeightOneSpectrum (𝓞 ℚ) := padicPlace 2 with hv₂
  set L : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v₂ (-1)) with hLdef
  have hL : η L = -1 := by
    have h := hu (-1)
    have e1 : (Units.map (padicRingEquiv 2).toMonoidHom
        (Units.map PadicInt.Coe.ringHom.toMonoidHom (-1 : ℤ_[2]ˣ))) = (-1 : (v₂.adicCompletion ℚ)ˣ) := by
      ext; simp
    have e2 : Units.map (PadicInt.toZModPow 2).toMonoidHom (-1 : ℤ_[2]ˣ) = -1 := by
      ext; simp
    rw [e1, e2, chi0_neg_one, inv_neg_one] at h
    exact h

  set A : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archCentralUnit ℚ w (-1) with hAdef
  set P : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
    Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) (-1) with hPdef
  have hP : η P = 1 := hfo.isIdeleClassChar (-1)
  have hPval : ((P : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = -1 := by
    show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) ((-1 : ℚˣ) : ℚ) = -1
    rw [Units.val_neg, Units.val_one, MonoidHom.coe_coe, map_neg, map_one]
  have hLval : ((L : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) =
      ((1 : InfiniteAdeleRing ℚ),
        ((localUnit (𝓞 ℚ) ℚ v₂ (-1) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) := rfl
  have hA1 : ((A : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w = (((-1 : (w.Completion)ˣ)) : w.Completion) :=
    archCentralUnit_fst_self w (-1)
  have hA2 : ((A : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := archCentralUnit_snd w (-1)

  have hr : η (A * L * P) = 1 := by
    refine hmod (A * L * P) ?_ ?_
    · rw [Units.val_mul, Units.val_mul, hPval, hLval]
      funext w'
      obtain rfl : w' = w := Subsingleton.elim _ _
      rw [adele_fst_mul, adele_fst_mul, adele_fst_neg, adele_fst_one, iar_mul_apply, iar_mul_apply, hA1,
        iar_neg_apply, iar_one_apply]
      dsimp only
      rw [iar_one_apply, Units.val_neg, Units.val_one]
      ring
    · intro v
      rw [Units.val_mul, Units.val_mul, hPval, hLval, adele_snd_mul, adele_snd_mul, hA2, adele_snd_neg,
        adele_snd_one, one_mul, far_mul_apply, far_neg_apply, far_one_apply]
      by_cases hv : v = v₂
      · subst hv
        rw [localUnit_apply_self, Units.val_neg, Units.val_one, neg_one_mul, neg_neg, sub_self,
          map_one, map_zero]
        exact ⟨rfl, zero_le'⟩
      · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v₂ (-1) hv, one_mul, Valuation.map_neg, map_one,
          idealMultiplicity_ratLevel_pow_eq_zero 2 hv, Nat.cast_zero, neg_zero, WithZero.exp_zero]
        refine ⟨rfl, ?_⟩
        calc Valued.v ((-1 : v.adicCompletion ℚ) - 1)
            ≤ max (Valued.v (-1 : v.adicCompletion ℚ)) (Valued.v (1 : v.adicCompletion ℚ)) :=
              Valuation.map_sub _ _ _
          _ = 1 := by rw [Valuation.map_neg, map_one, max_self]

  have hA : η A = -1 := by
    rw [map_mul, map_mul, hP, hL, mul_one] at hr
    have : η A = (η A * -1) * -1 := by rw [mul_assoc, neg_one_mul, neg_neg, mul_one]
    rw [this, hr, one_mul]

  intro x
  set r : ℝ := extensionEmbeddingOfIsReal hw (x : w.Completion) with hrdef
  have hxne : (x : w.Completion) ≠ 0 := x.ne_zero
  have hr_ne : r ≠ 0 := (map_ne_zero (extensionEmbeddingOfIsReal hw)).mpr hxne
  have hnorm : ‖(x : w.Completion)‖ = |r| := by
    rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x : w.Completion),
      Real.norm_eq_abs]
  have hemb : extensionEmbedding w (x : w.Completion) = (r : ℂ) :=
    (extensionEmbeddingOfIsReal_apply hw (x : w.Completion)).symm
  rw [mul_zero, Complex.cpow_zero, one_mul, zpow_one, hemb, hnorm]

  set e : w.Completion ≃+* ℝ := ringEquivRealOfIsReal hw with hedef
  have he : ∀ y : w.Completion, e y = extensionEmbeddingOfIsReal hw y := fun y => rfl
  have hpos_ne : e.symm |r| ≠ 0 := by
    intro h0
    have := congrArg e h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hr_ne (abs_eq_zero.mp this)
  set pos : (w.Completion)ˣ := Units.mk0 (e.symm |r|) hpos_ne with hposdef
  have hpos : archLocalChar η w pos = 1 := by
    rw [archLocalChar_apply]
    refine HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign ℚ η hfo.isOfFinOrder _ rfl fun τ => ?_
    show 0 < HeckeCharacter.archRealProjTau ℚ τ (archCentralUnit ℚ w pos)
    unfold HeckeCharacter.archRealProjTau
    obtain rfl : w = HeckeCharacter.placeOf ℚ τ := Subsingleton.elim _ _
    rw [archCentralUnit_fst_self]
    show 0 < e (e.symm |r|)
    rw [RingEquiv.apply_symm_apply]
    exact abs_pos.mpr hr_ne

  rcases lt_or_gt_of_ne hr_ne with hneg | hposr
  ·
    have hx : x = -1 * pos := by
      refine Units.ext (e.injective ?_)
      rw [Units.val_mul, map_mul, Units.val_neg, Units.val_one, map_neg, map_one]
      show e (x : w.Completion) = -1 * e (e.symm |r|)
      rw [RingEquiv.apply_symm_apply, abs_of_neg hneg, he, ← hrdef]; ring
    rw [hx, map_mul, hpos, mul_one]
    show ((η (archCentralUnit ℚ w (-1)) : ℂˣ) : ℂ) = _
    rw [← hAdef, hA, Units.val_neg, Units.val_one, abs_of_neg hneg, Complex.ofReal_neg,
      div_neg, div_self (Complex.ofReal_ne_zero.mpr hr_ne)]
  ·
    have hx : x = pos := by
      refine Units.ext (e.injective ?_)
      show e (x : w.Completion) = e (e.symm |r|)
      rw [RingEquiv.apply_symm_apply, abs_of_pos hposr, he, ← hrdef]
    rw [hx, hpos, Units.val_one, abs_of_pos hposr, div_self (Complex.ofReal_ne_zero.mpr hr_ne)]

end LTOddTwist

end

theorem solution :
    ∃ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ ∧
      ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 1 :=
  LTOddTwist.main

end S_LanglandsTunnell_Converse_exists_odd_isAdmissibleTwist
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_odd_isAdmissibleTwist (solution)
