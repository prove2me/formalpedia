-- Prove2me | solution 1 for NumberField.AdelicLevel.finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dcafd852-85b7-537b-a61e-78041c79b051

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section Part03
open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm
open AutomorphicForm.WindowedSiegel UpperHalfPlane
noncomputable section
namespace AdelicDescentHK
section OmegaInfra
private abbrev h4pins : CarrierPins ℚ := productionPinsCompact ℚ

variable {Ψ : HeckeEigensystem ℚ ℂ}
end OmegaInfra
end AdelicDescentHK
end
end Part03
section Part04
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open AutomorphicForm MeasureTheory
noncomputable section
namespace AdelicDescentHK
section RatPrimeFacts
private theorem natGenerator_ratPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (ratPrime p) = (p : ℕ) :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

private theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℤ)) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from
      (map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n).symm,
    Ideal.apply_mem_of_equiv_iff]

end RatPrimeFacts
section RatPrimeNorm
private theorem intEquiv_dvd_iff (x y : 𝓞 ℚ) :
    x ∣ y ↔ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x ∣ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) y := by
  constructor
  · exact fun h => map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
  · intro h
    have h2 := map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm h
    simpa only [RingEquiv.symm_apply_apply] using h2

private theorem ratPrime_asIdeal_eq_span (p : Nat.Primes) :
    (ratPrime p).asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := by
  ext x
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x
        ∈ (ratPrime p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
      Ideal.apply_mem_of_equiv_iff.mpr hx
    rw [← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_ratPrime,
      Ideal.mem_span_singleton] at h1
    rw [intEquiv_dvd_iff]
    simpa using h1
  · intro hx
    have h1 : ((p : ℕ) : ℤ) ∣ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x := by
      have h2 := (intEquiv_dvd_iff _ x).mp hx
      simpa using h2
    have h2 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x
        ∈ (ratPrime p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
      rw [← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_ratPrime,
        Ideal.mem_span_singleton]
      exact h1
    exact Ideal.apply_mem_of_equiv_iff.mp h2

end RatPrimeNorm
section PrimeSplit
variable {Ψ : HeckeEigensystem ℚ ℂ}
private noncomputable def pUnit (p : Nat.Primes) : ((ratPrime p).adicCompletion ℚ)ˣ :=
  Units.mk0 (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    (by
      refine (map_ne_zero _).mpr ?_
      exact_mod_cast p.2.pos.ne')

end PrimeSplit
section RestKill
variable {Ψ : HeckeEigensystem ℚ ℂ}
private theorem eq_ratPrime_of_natCast_mem (p : Nat.Primes) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hmem : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = ratPrime p := by
  have h1 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w ∣ (p : ℕ) :=
    (natCast_mem_asIdeal_iff w _).mp hmem
  have h2 : Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w = (p : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq
      (Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) w) p.2).mp h1
  have h3 : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = p := Subtype.ext h2
  have h4 := congrArg (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm h3
  rwa [Equiv.symm_apply_apply] at h4

end RestKill
end AdelicDescentHK
end
end Part04
section Part06
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne
open scoped MatrixGroups ModularForm
noncomputable section
namespace AdelicDescentHK
variable {Ψ : HeckeEigensystem ℚ ℂ}
private def upperTriQ (a b d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by
    simp only [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero ha hd)

section S5SupplyVal
private theorem isUnit_adicInt_of_valued_eq_one {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x : v.adicCompletionIntegers ℚ} (hx : Valued.v (x : v.adicCompletion ℚ) = 1) :
    IsUnit x := by
  have hx0 : (x : v.adicCompletion ℚ) ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hmem : (x : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  exact ⟨⟨x, ⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

private noncomputable def natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    v.adicCompletionIntegers ℚ :=
  ⟨algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ), by
    rw [mem_adicCompletionIntegers,
      show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp,
      valued_algebraMap]
    exact v.intValuation_le_one _⟩

private theorem valued_natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((natInt v n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = v.intValuation (((n : ℕ) : 𝓞 ℚ)) := by
  show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = _
  rw [show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp, valued_algebraMap]

private noncomputable def pInt (p : Nat.Primes) : (ratPrime p).adicCompletionIntegers ℚ :=
  natInt (ratPrime p) (p : ℕ)

private theorem isUnit_natInt_of_not_dvd (p : Nat.Primes) {n : ℕ} (hnp : ¬ (p : ℕ) ∣ n) :
    IsUnit (natInt (ratPrime p) n) := by
  apply isUnit_adicInt_of_valued_eq_one
  rw [valued_natInt]
  have hmem : ((n : ℕ) : 𝓞 ℚ) ∉ (ratPrime p).asIdeal := by
    rw [ratPrime_asIdeal_eq_span p, Ideal.mem_span_singleton]
    intro hdvd
    apply hnp
    have h2 := (intEquiv_dvd_iff _ _).mp hdvd
    rw [map_natCast, map_natCast] at h2
    exact_mod_cast h2
  refine le_antisymm ((ratPrime p).intValuation_le_one _) (not_lt.mp ?_)
  intro hcon
  exact hmem (((ratPrime p).intValuation_lt_one_iff_mem _).mp hcon)

end S5SupplyVal
section S5F4Supply
private theorem glArch_heckeGenAt_unit (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (t : ((v.adicCompletion ℚ))ˣ) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ v t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst t i j

private theorem finComponent_glFin_heckeGenAt_of_ne (p : Nat.Primes)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime p) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
      (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  exact heckeGenAt_snd_apply_of_ne (pUnit p) hw i j

private theorem hpInt_ne (p : Nat.Primes) :
    algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
      (pInt p) ≠ 0 :=
  (pUnit p).ne_zero

private theorem finComponent_glFin_heckeGenAt_self (p : Nat.Primes) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = LocalGL2.diagPi (pInt p) (hpInt_ne p) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))) :
        Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ)) i j
      = ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 (ratPrime p) := rfl
  rw [hL, heckeGenAt_snd_apply_self (pUnit p) i j, LocalGL2.coe_diagPi]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_globalPoints_apply_place (γ : GL (Fin 2) ℚ) (i j : Fin 2)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
      = algebraMap ℚ (w.adicCompletion ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
  congrArg (fun f : ℚ →+* w.adicCompletion ℚ => f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j))
    (by apply RingHom.ext_rat :
      ((finAdeleEval (𝓞 ℚ) ℚ w).comp
          ((RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
            (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))
        = algebraMap ℚ (w.adicCompletion ℚ))

end S5F4Supply
section S7Supply
private theorem isUnit_natInt_p_of_ne (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    IsUnit (natInt w p) := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat.Primes, ratPrime q = w :=
    ⟨Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w,
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply w⟩
  refine isUnit_natInt_of_not_dvd q fun hdvd => hw ?_
  have hqp : (q : ℕ) = p :=
    (Nat.prime_dvd_prime_iff_eq q.2 hp).mp hdvd
  exact congrArg ratPrime (Subtype.ext hqp)

private theorem finComponent_glFin_globalPoints_diag_self (p : ℕ) (hp : p.Prime) :
    finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      = LocalGL2.diagPi (pInt ⟨p, hp⟩) (hpInt_ne ⟨p, hp⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) ((ratPrime ⟨p, hp⟩).adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ (p : ℚ) 0 1
          (by exact_mod_cast hp.pos.ne') one_ne_zero)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) (ratPrime ⟨p, hp⟩) from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) ((p : ℚ))
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (pInt ⟨p, hp⟩)
    rfl
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 0
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 0
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime ⟨p, hp⟩).adicCompletionIntegers ℚ)
          ((ratPrime ⟨p, hp⟩).adicCompletion ℚ) 1
    rw [map_one, map_one]

private noncomputable def diagUnitAt (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    GL (Fin 2) (w.adicCompletion ℚ) :=
  ⟨!![algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)), 0; 0, 1],
    !![((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
        w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ), 0; 0, 1],
    by
      have h2 : (natInt w p)
          * (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
            w.adicCompletionIntegers ℚ) = 1 :=
        (isUnit_natInt_p_of_ne p hp hw).mul_val_inv
      have h1 : algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ))
          * ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
              w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ) = 1 := by
        have h3 := congrArg
          (fun x : w.adicCompletionIntegers ℚ => (x : w.adicCompletion ℚ)) h2
        exact h3
      rw [Matrix.mul_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp <;> simpa using h1
    , by
      have h2 : (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
            w.adicCompletionIntegers ℚ) * (natInt w p) = 1 :=
        (isUnit_natInt_p_of_ne p hp hw).val_inv_mul
      have h1 : ((((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ : (w.adicCompletionIntegers ℚ)ˣ) :
              w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ)
          * algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)) = 1 := by
        have h3 := congrArg
          (fun x : w.adicCompletionIntegers ℚ => (x : w.adicCompletion ℚ)) h2
        exact h3
      rw [Matrix.mul_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp <;> simpa using h1⟩

private theorem finComponent_glFin_globalPoints_diag_of_ne (p : ℕ) (hp : p.Prime)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime ⟨p, hp⟩) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      = diagUnitAt p hp hw := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ (p : ℚ) 0 1
          (by exact_mod_cast hp.pos.ne') one_ne_zero)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · rfl
  · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) = 0
    rw [map_zero]
  · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) = 0
    rw [map_zero]
  · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) = 1
    rw [map_one]

private theorem heckeGenAt_inv_mul_finEmbed_global_diag_mem_U (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) :
    (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      ∈ h4pins.U L := by

  have hcompv : finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ
      ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))))) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_heckeGenAt_self,
      finComponent_glFin_globalPoints_diag_self p hp]
    exact inv_mul_cancel _
  have hcompw : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      ∀ hw : w ≠ ratPrime ⟨p, hp⟩,
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
        ((heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
          * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))))
        = diagUnitAt p hp hw := by
    intro w hw
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
      finComponent_glFin_globalPoints_diag_of_ne p hp hw]
    rw [inv_one, one_mul]

  rw [productionPinsCompact_U, Subgroup.mem_inf]
  set T : AdelicGL2 (𝓞 ℚ) ℚ :=
    (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero))) with hT
  have hcomp : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => rfl
  have hcompinv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T))⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => by
    rw [show ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T)⁻¹) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) from rfl, map_inv]
  constructor
  · refine mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩)
    ·
      refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcomp w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply_eq, Matrix.one_apply] <;>
            first
            | exact one_mem _
            | exact zero_mem _
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (natInt w (p : ℕ)).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
          from rfl, hcomp w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcomp w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
    ·
      refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcompinv w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply] <;>
            (split <;> first | exact one_mem _ | exact zero_mem _)
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ :
              (w.adicCompletionIntegers ℚ)ˣ) : w.adicCompletionIntegers ℚ).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w from rfl,
          hcompinv w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((((glFin (𝓞 ℚ) ℚ T)⁻¹ :
              GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcompinv w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
  ·
    refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩),
      AdelicDock.glArch_finEmbed, inv_one, one_mul]

end S7Supply
section H7Heads
section S7Value
private theorem finEmbed_global_diag_mul_heckeGenAt_inv_mem_U (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹
      ∈ h4pins.U L := by
  have hcompv : finComponent (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (glFin (𝓞 ℚ) ℚ
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_globalPoints_diag_self p hp,
      finComponent_glFin_heckeGenAt_self]
    exact mul_inv_cancel _
  have hcompw : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      ∀ hw : w ≠ ratPrime ⟨p, hp⟩,
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ
        (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
          * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹))
        = diagUnitAt p hp hw := by
    intro w hw
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      finComponent_glFin_globalPoints_diag_of_ne p hp hw,
      finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw]
    rw [inv_one, mul_one]
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  set T : AdelicGL2 (𝓞 ℚ) ℚ :=
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ (p : ℚ) 0 1 (by exact_mod_cast hp.pos.ne') one_ne_zero)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ with hT
  have hcomp : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => rfl
  have hcompinv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ∀ i j : Fin 2,
      ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((((finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T))⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) := fun w i j => by
    rw [show ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((finComponent (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T)⁻¹) :
            Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) from rfl, map_inv]
  constructor
  · refine mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩)
    · refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcomp w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply_eq, Matrix.one_apply] <;>
            first
            | exact one_mem _
            | exact zero_mem _
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (natInt w (p : ℕ)).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
          from rfl, hcomp w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((glFin (𝓞 ℚ) ℚ T : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcomp w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
    · refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · rw [hcompinv w i j]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          fin_cases i <;> fin_cases j <;>
            simp only [Units.val_one, Matrix.one_apply] <;>
            (split <;> first | exact one_mem _ | exact zero_mem _)
        · rw [hcompw w hw]
          fin_cases i <;> fin_cases j
          · exact (((isUnit_natInt_p_of_ne p hp hw).unit⁻¹ :
              (w.adicCompletionIntegers ℚ)ˣ) : w.adicCompletionIntegers ℚ).2
          · exact zero_mem _
          · exact zero_mem _
          · exact one_mem _
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0)) w
          = ((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w from rfl,
          hcompinv w 1 0]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_ne one_ne_zero, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v (0 : w.adicCompletion ℚ) ≤ _
          rw [map_zero]
          exact zero_le'
      · rw [show (((((glFin (𝓞 ℚ) ℚ T)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1)) w
          = finAdeleEval (𝓞 ℚ) ℚ w ((((glFin (𝓞 ℚ) ℚ T)⁻¹ :
              GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
          map_sub, map_one, finAdeleEval_apply, hcompinv w 1 1]
        by_cases hw : w = ratPrime ⟨p, hp⟩
        · subst hw; rw [hcompv, inv_one]
          simp only [Units.val_one, Matrix.one_apply_eq, sub_self, map_zero]
          exact zero_le'
        · rw [hcompw w hw]
          show Valued.v ((1 : w.adicCompletion ℚ) - 1) ≤ _
          rw [sub_self, map_zero]
          exact zero_le'
  · refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, AdelicDock.glArch_finEmbed,
      glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩), inv_one, mul_one]

end S7Value
end H7Heads
end AdelicDescentHK
end
end Part06

namespace AdelicDescentHK
open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm
theorem pUnit_eq_of_val_eq (p : Nat.Primes) (ϖ : ((ratPrime p).adicCompletion ℚ)ˣ)
    (hϖ : (ϖ : (ratPrime p).adicCompletion ℚ) = algebraMap ℚ _ ((p : ℕ) : ℚ)) :
    ϖ = pUnit p := Units.ext hϖ
end AdelicDescentHK

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SiegelCoordinates IsDedekindDomain AdelicDescentHK in

theorem solution
    (L : Ideal (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ)) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero)))
        * (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹ ∈ levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ ∧
    (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero)))
      ∈ levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ := by
  obtain rfl : v = ratPrime ⟨p, hp⟩ := eq_ratPrime_of_natCast_mem ⟨p, hp⟩ hv
  obtain rfl : ϖ = pUnit ⟨p, hp⟩ := pUnit_eq_of_val_eq ⟨p, hp⟩ ϖ hϖ
  exact ⟨finEmbed_global_diag_mul_heckeGenAt_inv_mem_U p hp L,
    heckeGenAt_inv_mul_finEmbed_global_diag_mem_U p hp L⟩

end S_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat
end P2MW
export P2MW.S_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat (solution)
