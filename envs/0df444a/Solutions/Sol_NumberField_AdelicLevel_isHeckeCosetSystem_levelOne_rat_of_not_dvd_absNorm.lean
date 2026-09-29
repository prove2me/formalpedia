-- Prove2me | solution 1 for NumberField.AdelicLevel.isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/61ec5b5a-e133-5f71-8fd5-18d43a12edaa

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

namespace P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section Part02
noncomputable section
namespace AdelicDescentHE
open MeasureTheory NumberField AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicHaar NumberField.AdelicLevel Set
p2m_open "AdelicDock IsDedekindDomain NumberField.InfinitePlace.Completion"
open scoped Real
open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AdelicDock AutomorphicForm
open MeasureTheory IsDedekindDomain
private theorem glpair_ext {g h : AdelicGL2 (𝓞 ℚ) ℚ}
    (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) ha
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hf

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
p2m_open "MeasureTheory NumberField.InfinitePlace.Completion"
open AutomorphicForm.SiegelCoordinates
open MeasureTheory NumberField AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicHaar NumberField.AdelicLevel Set
open scoped Real
end AdelicDescentHE
end
end Part02
section Part03
open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm
open AutomorphicForm.WindowedSiegel UpperHalfPlane
noncomputable section
namespace AdelicDescentHE
section OmegaInfra
private abbrev H4Ad := AdeleRing (𝓞 ℚ) ℚ

private abbrev h4pins : CarrierPins ℚ := productionPinsCompact ℚ

variable {Ψ : HeckeEigensystem ℚ ℂ}
end OmegaInfra
end AdelicDescentHE
end
end Part03
section Part04
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open AutomorphicForm MeasureTheory
noncomputable section
namespace AdelicDescentHE
section KillAssembler
private theorem glFin_centralScalar_entry (w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (i j : Fin 2) :
    ((glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) w)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
      = Matrix.diagonal (fun _ => (w : FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := by
  rw [glFin_apply]
  show adeleFin (𝓞 ℚ) ℚ (Matrix.diagonal
    (fun _ => (finIncl (𝓞 ℚ) ℚ (w : FiniteAdeleRing (𝓞 ℚ) ℚ) : H4Ad)) i j) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]

end KillAssembler
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

private theorem absNorm_ratPrime (p : Nat.Primes) :
    Ideal.absNorm (ratPrime p).asIdeal = (p : ℕ) := by
  rw [ratPrime_asIdeal_eq_span, Ideal.absNorm_span_singleton,
    show (((p : ℕ) : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) ((p : ℕ) : ℤ) by simp,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  simp

end RatPrimeNorm
section PrimeSplit
variable {Ψ : HeckeEigensystem ℚ ℂ}
private noncomputable def pUnit (p : Nat.Primes) : ((ratPrime p).adicCompletion ℚ)ˣ :=
  Units.mk0 (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    (by
      refine (map_ne_zero _).mpr ?_
      exact_mod_cast p.2.pos.ne')

private theorem valued_pUnit (p : Nat.Primes) :
    Valued.v ((pUnit p : ((ratPrime p).adicCompletion ℚ))) = WithZero.exp (-1 : ℤ) := by
  show Valued.v (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    = WithZero.exp (-1 : ℤ)
  rw [show (((p : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((p : ℕ) : 𝓞 ℚ)) by simp,
    valued_algebraMap]
  exact intValuation_singleton _ (by exact_mod_cast p.2.pos.ne')
    (ratPrime_asIdeal_eq_span p)

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
end AdelicDescentHE
end
end Part04
section Part05
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne
open scoped MatrixGroups ModularForm
noncomputable section
namespace AdelicDescentHE
section PeelSupply
variable {L : Ideal (𝓞 ℚ)}
variable {L : Ideal (𝓞 ℚ)}
private theorem finEmbed_scalar_eq_centralScalar (e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) e)
      = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) e) := by
  apply glpair_ext
  · rw [AdelicDock.glArch_finEmbed]
    symm
    ext i j
    rw [glArch_apply]
    show adeleArch (𝓞 ℚ) ℚ (Matrix.diagonal
      (fun _ => (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ) : H4Ad)) i j)
      = ((1 : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) _) i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      have h1 : adeleArch (𝓞 ℚ) ℚ (finIncl (𝓞 ℚ) ℚ (e : FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := rfl
      rw [h1, Units.val_one, Matrix.one_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero, Units.val_one, Matrix.one_apply_ne h]
  · rw [AdelicDock.glFin_finEmbed]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glFin_centralScalar_entry,
      show ((Matrix.GeneralLinearGroup.scalar (Fin 2) e :
          GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        = Matrix.scalar (Fin 2) ((e : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl]
    by_cases h : i = j
    · subst h
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, h]

end PeelSupply
end AdelicDescentHE
end
end Part05
section Part06
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open UpperHalfPlane CongruenceSubgroup ModularForm EisensteinWeightOne
open scoped MatrixGroups ModularForm
noncomputable section
namespace AdelicDescentHE
variable {Ψ : HeckeEigensystem ℚ ℂ}
private def upperTriQ (a b d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by
    simp only [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero ha hd)

private noncomputable def heckeReps (p : ℕ) (hp : p.Prime) :
    Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ :=
  fun i =>
    if (i : ℕ) < p then
      AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
        * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)
    else
      centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹

section S5SupplyVal
private theorem withZero_exp_le_exp {a b : ℤ} : WithZero.exp a ≤ WithZero.exp b ↔ a ≤ b := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe]
  exact Multiplicative.ofAdd_le

private theorem withZero_exp_lt_exp {a b : ℤ} : WithZero.exp a < WithZero.exp b ↔ a < b := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, WithZero.coe_lt_coe]
  exact Multiplicative.ofAdd_lt

private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx0 : x ≠ 0)
    (hx1 : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.exp_log hx0] at hx1 ⊢
  rw [← WithZero.exp_zero, withZero_exp_lt_exp] at hx1
  exact withZero_exp_le_exp.mpr (by omega)

private theorem valued_adicInt_le_one {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (x : v.adicCompletionIntegers ℚ) :
    Valued.v (x : v.adicCompletion ℚ) ≤ 1 := by
  have h := x.2
  rwa [mem_adicCompletionIntegers] at h

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

private theorem valued_eq_one_of_isUnit {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x : v.adicCompletionIntegers ℚ} (hx : IsUnit x) :
    Valued.v (x : v.adicCompletion ℚ) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      * (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
          : v.adicCompletion ℚ) = 1 := by
    exact_mod_cast congrArg Subtype.val u.mul_inv
  have h2 := congrArg Valued.v h1
  rw [map_mul, map_one] at h2
  refine le_antisymm (valued_adicInt_le_one _) ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
        * Valued.v (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ)
            : v.adicCompletion ℚ) := h2.symm
    _ ≤ Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * 1 :=
        mul_le_mul' le_rfl (valued_adicInt_le_one _)
    _ = Valued.v ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := mul_one _

private theorem adicInt_dvd_of_valued_le {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    {x y : v.adicCompletionIntegers ℚ} (hx0 : (x : v.adicCompletion ℚ) ≠ 0)
    (h : Valued.v (y : v.adicCompletion ℚ) ≤ Valued.v (x : v.adicCompletion ℚ)) :
    x ∣ y := by
  have hvx : Valued.v (x : v.adicCompletion ℚ) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hx0
  have hmem : (y : v.adicCompletion ℚ) / (x : v.adicCompletion ℚ)
      ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_div₀, div_eq_mul_inv]
    calc Valued.v (y : v.adicCompletion ℚ) * (Valued.v (x : v.adicCompletion ℚ))⁻¹
        ≤ Valued.v (x : v.adicCompletion ℚ) * (Valued.v (x : v.adicCompletion ℚ))⁻¹ :=
          mul_le_mul' h le_rfl
      _ = 1 := mul_inv_cancel₀ hvx
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  show (y : v.adicCompletion ℚ)
      = (x : v.adicCompletion ℚ) * ((y : v.adicCompletion ℚ) / (x : v.adicCompletion ℚ))
  rw [mul_comm]
  exact (div_mul_cancel₀ _ hx0).symm

private noncomputable def natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    v.adicCompletionIntegers ℚ :=
  ⟨algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ), by
    rw [mem_adicCompletionIntegers,
      show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp,
      valued_algebraMap]
    exact v.intValuation_le_one _⟩

@[scoped simp] private theorem coe_natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((natInt v n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ) := rfl

private theorem valued_natInt (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v ((natInt v n : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = v.intValuation (((n : ℕ) : 𝓞 ℚ)) := by
  show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((n : ℕ) : ℚ)) = _
  rw [show (((n : ℕ) : ℚ)) = algebraMap (𝓞 ℚ) ℚ (((n : ℕ) : 𝓞 ℚ)) by simp, valued_algebraMap]

private noncomputable def pInt (p : Nat.Primes) : (ratPrime p).adicCompletionIntegers ℚ :=
  natInt (ratPrime p) (p : ℕ)

private theorem valued_pInt (p : Nat.Primes) :
    Valued.v ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
        : (ratPrime p).adicCompletion ℚ)
      = WithZero.exp (-1 : ℤ) := valued_pUnit p

private theorem irreducible_pInt (p : Nat.Primes) : Irreducible (pInt p) := by
  constructor
  · intro hu
    have h1 := valued_eq_one_of_isUnit hu
    rw [valued_pInt, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_inj.mp h1
    omega
  · intro a b hab
    by_contra hcon
    push Not at hcon
    have ha1 : Valued.v ((a : (ratPrime p).adicCompletion ℚ)) < 1 :=
      lt_of_le_of_ne (valued_adicInt_le_one _)
        (fun h => hcon.1 (isUnit_adicInt_of_valued_eq_one h))
    have hb1 : Valued.v ((b : (ratPrime p).adicCompletion ℚ)) < 1 :=
      lt_of_le_of_ne (valued_adicInt_le_one _)
        (fun h => hcon.2 (isUnit_adicInt_of_valued_eq_one h))
    have hco : ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)
        = (a : (ratPrime p).adicCompletion ℚ) * (b : (ratPrime p).adicCompletion ℚ) := by
      exact_mod_cast congrArg Subtype.val hab
    have hv : WithZero.exp (-1 : ℤ)
        = Valued.v ((a : (ratPrime p).adicCompletion ℚ))
          * Valued.v ((b : (ratPrime p).adicCompletion ℚ)) := by
      rw [← map_mul, ← hco, valued_pInt]
    have ha0 : Valued.v ((a : (ratPrime p).adicCompletion ℚ)) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hv
      exact WithZero.exp_ne_zero hv
    have hb0 : Valued.v ((b : (ratPrime p).adicCompletion ℚ)) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hv
      exact WithZero.exp_ne_zero hv
    have hle : Valued.v ((a : (ratPrime p).adicCompletion ℚ))
          * Valued.v ((b : (ratPrime p).adicCompletion ℚ))
        ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) :=
      mul_le_mul' (le_exp_neg_one_of_lt_one ha0 ha1) (le_exp_neg_one_of_lt_one hb0 hb1)
    rw [← hv, ← WithZero.exp_add] at hle
    have h3 := withZero_exp_le_exp.mp hle
    omega

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
section S5SupplyRes
private theorem valued_ball_one_mem_nhds {R : Type*} {Γ₀ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀] (b : R) :
    { y : R | Valued.v (y - b) < (1 : Γ₀) } ∈ nhds b := by
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_one] at hy
  have h1 : Valued.v.restrict (y - b) < Valued.v.restrict 1 := by rwa [map_one]
  rw [Valuation.restrict_lt_iff] at h1
  simpa using h1

private theorem exists_rat_valued_sub_lt_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (b : v.adicCompletion ℚ) :
    ∃ q : ℚ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q - b)
      < (1 : WithZero (Multiplicative ℤ)) :=
  (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap ℚ v).mem_nhds
    (valued_ball_one_mem_nhds b)

private theorem exists_intRing_valued_sub_lt_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (b : v.adicCompletionIntegers ℚ) :
    ∃ a : 𝓞 ℚ, Valued.v ((b : v.adicCompletion ℚ)
        - algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)) < 1 := by
  obtain ⟨q, hq⟩ := exists_rat_valued_sub_lt_one v (b : v.adicCompletion ℚ)
  have hswap : Valued.v ((b : v.adicCompletion ℚ)
      - algebraMap ℚ (v.adicCompletion ℚ) q) < 1 := by
    rwa [Valued.v.map_sub_swap]
  have hq1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
    have h1 : algebraMap ℚ (v.adicCompletion ℚ) q
        = (b : v.adicCompletion ℚ)
          - ((b : v.adicCompletion ℚ) - algebraMap ℚ (v.adicCompletion ℚ) q) := by ring
    rw [h1]
    exact Valued.v.map_sub_le (valued_adicInt_le_one b) hswap.le
  have hqK : v.valuation ℚ q ≤ 1 := by
    calc v.valuation ℚ q
        = Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) :=
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q).symm
      _ ≤ 1 := hq1
  obtain ⟨a, ha⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hqK 1
  refine ⟨a, ?_⟩
  have haC : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
      - algebraMap ℚ (v.adicCompletion ℚ) q) < 1 := by
    rw [← map_sub]
    calc Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a - q))
        = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ a - q) :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      _ < 1 := by simpa using ha
  have hfinal : (b : v.adicCompletion ℚ)
      - algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
      = ((b : v.adicCompletion ℚ) - algebraMap ℚ (v.adicCompletion ℚ) q)
        - (algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
            - algebraMap ℚ (v.adicCompletion ℚ) q) := by ring
  rw [hfinal]
  exact Valued.v.map_sub_lt hswap haC

private theorem exists_nat_sub_mem_ratPrime (p : Nat.Primes) (a : 𝓞 ℚ) :
    ∃ n : ℕ, n < (p : ℕ) ∧ a - ((n : ℕ) : 𝓞 ℚ) ∈ (ratPrime p).asIdeal := by
  haveI : NeZero (p : ℕ) := ⟨p.2.pos.ne'⟩
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) a with hz
  refine ⟨(z : ZMod (p : ℕ)).val, ZMod.val_lt _, ?_⟩
  rw [ratPrime_asIdeal_eq_span, Ideal.mem_span_singleton, intEquiv_dvd_iff,
    map_natCast, map_sub, map_natCast, ← hz]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_self]

private theorem valued_le_exp_neg_one_of_mem (p : Nat.Primes) {x : 𝓞 ℚ}
    (hx : x ∈ (ratPrime p).asIdeal) :
    Valued.v (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ x))
      ≤ WithZero.exp (-1 : ℤ) := by
  rw [valued_algebraMap]
  rcases eq_or_ne ((ratPrime p).intValuation x) 0 with h0 | h0
  · rw [h0]; exact zero_le'
  · exact le_exp_neg_one_of_lt_one h0
      (((ratPrime p).intValuation_lt_one_iff_mem _).mpr hx)

private theorem exists_natInt_dvd_sub (p : Nat.Primes)
    (b : (ratPrime p).adicCompletionIntegers ℚ) :
    ∃ n : ℕ, n < (p : ℕ) ∧ pInt p ∣ (b - natInt (ratPrime p) n) := by
  obtain ⟨a, ha⟩ := exists_intRing_valued_sub_lt_one (ratPrime p) b
  obtain ⟨n, hn, hmem⟩ := exists_nat_sub_mem_ratPrime p a
  refine ⟨n, hn, ?_⟩
  have hban : Valued.v ((b : (ratPrime p).adicCompletion ℚ)
      - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)) ≤ WithZero.exp (-1 : ℤ) := by
    have hsplit : (b : (ratPrime p).adicCompletion ℚ)
        - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ)
        = ((b : (ratPrime p).adicCompletion ℚ)
            - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a))
          + (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
              - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
                  : (ratPrime p).adicCompletion ℚ)) := by ring
    rw [hsplit]
    refine Valued.v.map_add_le ?_ ?_
    · rcases eq_or_ne (Valued.v ((b : (ratPrime p).adicCompletion ℚ)
          - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a))) 0
        with h0 | h0
      · rw [h0]; exact zero_le'
      · exact le_exp_neg_one_of_lt_one h0 ha
    · have hcoe : algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ a)
          - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
              : (ratPrime p).adicCompletion ℚ)
          = algebraMap ℚ ((ratPrime p).adicCompletion ℚ)
              (algebraMap (𝓞 ℚ) ℚ (a - ((n : ℕ) : 𝓞 ℚ))) := by
        rw [coe_natInt, map_sub, map_sub]
        congr 1
      rw [hcoe]
      exact valued_le_exp_neg_one_of_mem p hmem
  have hpne : ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
      : (ratPrime p).adicCompletion ℚ) ≠ 0 := by
    intro h
    have h2 := valued_pInt p
    rw [h, map_zero] at h2
    exact WithZero.exp_ne_zero h2.symm
  apply adicInt_dvd_of_valued_le hpne
  rw [valued_pInt]
  calc Valued.v (((b - natInt (ratPrime p) n) : (ratPrime p).adicCompletionIntegers ℚ)
        : (ratPrime p).adicCompletion ℚ)
      = Valued.v ((b : (ratPrime p).adicCompletion ℚ)
          - ((natInt (ratPrime p) n : (ratPrime p).adicCompletionIntegers ℚ)
              : (ratPrime p).adicCompletion ℚ)) := by norm_cast
    _ ≤ WithZero.exp (-1 : ℤ) := hban

end S5SupplyRes
section S5SupplyW
open scoped Classical in
private noncomputable def finDelta (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1,
    Filter.Eventually.of_forall fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact one_mem _
      · rw [Function.update_of_ne hw]; exact zero_mem _⟩

open scoped Classical in
private noncomputable def finCoDelta (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0,
    Filter.Eventually.of_forall fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact zero_mem _
      · rw [Function.update_of_ne hw]; exact one_mem _⟩

open scoped Classical in
private theorem finDelta_apply_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v v = 1 := by
  show Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1 v = 1
  rw [Function.update_self]

open scoped Classical in
private theorem finDelta_apply_of_ne {v w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : finDelta v w = 0 := by
  show Function.update (0 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 1 w = 0
  rw [Function.update_of_ne hw]
  rfl

open scoped Classical in
private theorem finCoDelta_apply_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v v = 0 := by
  show Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0 v = 0
  rw [Function.update_self]

open scoped Classical in
private theorem finCoDelta_apply_of_ne {v w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : finCoDelta v w = 1 := by
  show Function.update (1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      w.adicCompletion ℚ) v 0 w = 1
  rw [Function.update_of_ne hw]
  rfl

private theorem finDelta_mem_integral (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun w => by
  by_cases hw : w = v
  · subst hw; rw [finDelta_apply_self]; exact one_mem _
  · rw [finDelta_apply_of_ne hw]; exact zero_mem _

private theorem finCoDelta_mem_integral (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun w => by
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self]; exact zero_mem _
  · rw [finCoDelta_apply_of_ne hw]; exact one_mem _

private theorem finCoDelta_sq_add_finDelta_sq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v * finCoDelta v + finDelta v * finDelta v = 1 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finCoDelta v * finCoDelta v + finDelta v * finDelta v) w
      = (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finCoDelta_mul_finDelta_add_finDelta_mul_finCoDelta
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finCoDelta v * finDelta v + finDelta v * finCoDelta v = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finCoDelta v * finDelta v + finDelta v * finCoDelta v) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finDelta_mul_finCoDelta_add_finCoDelta_mul_finDelta
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v * finCoDelta v + finCoDelta v * finDelta v = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finDelta v * finCoDelta v + finCoDelta v * finDelta v) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem finDelta_sq_add_finCoDelta_sq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    finDelta v * finDelta v + finCoDelta v * finCoDelta v = 1 := by
  refine Subtype.ext (funext fun w => ?_)
  show (finDelta v * finDelta v + finCoDelta v * finCoDelta v) w
      = (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  rw [coe_add_apply, coe_mul_apply, coe_mul_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw; rw [finCoDelta_apply_self, finDelta_apply_self]; ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]; ring

private theorem weylMat_mul_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    (!![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
        * !![finCoDelta v, finDelta v; finDelta v, finCoDelta v])
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two,
    finCoDelta_sq_add_finDelta_sq,
    finCoDelta_mul_finDelta_add_finDelta_mul_finCoDelta,
    finDelta_mul_finCoDelta_add_finCoDelta_mul_finDelta,
    finDelta_sq_add_finCoDelta_sq]

private noncomputable def weylFin (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  val := !![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
  inv := !![finCoDelta v, finDelta v; finDelta v, finCoDelta v]
  val_inv := weylMat_mul_self v
  inv_val := weylMat_mul_self v

private theorem ratPrime_not_dvd_of_not_dvd_absNorm (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    ¬ (ratPrime p).asIdeal ∣ L ∧ L ≠ ⊥ := by
  have key : (ratPrime p).asIdeal ∣ L → False := by
    intro h
    apply hpN
    have h2 := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h)
    rwa [absNorm_ratPrime] at h2
  refine ⟨key, fun hbot => key ?_⟩
  rw [hbot, ← Ideal.zero_eq_bot]
  exact dvd_zero _

private theorem finDelta_mem_idealBall (p : Nat.Primes) {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    (hdvd : ¬ (ratPrime p).asIdeal ∣ L) :
    finDelta (ratPrime p) ∈ idealBall (𝓞 ℚ) ℚ L := fun w => by
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finDelta_apply_self, map_one, idealBound_eq_one_of_not_dvd hL hdvd]
  · rw [finDelta_apply_of_ne hw, map_zero]; exact zero_le'

private theorem finCoDelta_sub_one_mem_idealBall (p : Nat.Primes) {L : Ideal (𝓞 ℚ)} (hL : L ≠ ⊥)
    (hdvd : ¬ (ratPrime p).asIdeal ∣ L) :
    finCoDelta (ratPrime p) - 1 ∈ idealBall (𝓞 ℚ) ℚ L := fun w => by
  rw [coe_sub_apply, coe_one_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, zero_sub, Valuation.map_neg, map_one,
      idealBound_eq_one_of_not_dvd hL hdvd]
  · rw [finCoDelta_apply_of_ne hw, sub_self, map_zero]; exact zero_le'

private theorem weylFin_isLevelOneMatrix (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((weylFin (ratPrime p) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  obtain ⟨hdvd, hbot⟩ := ratPrime_not_dvd_of_not_dvd_absNorm p hpN
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j
    · show finCoDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finCoDelta_mem_integral _
    · show finDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finDelta_mem_integral _
    · show finDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finDelta_mem_integral _
    · show finCoDelta (ratPrime p) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ
      exact finCoDelta_mem_integral _
  · show finDelta (ratPrime p) ∈ idealBall (𝓞 ℚ) ℚ L
    exact finDelta_mem_idealBall p hbot hdvd
  · show finCoDelta (ratPrime p) - 1 ∈ idealBall (𝓞 ℚ) ℚ L
    exact finCoDelta_sub_one_mem_idealBall p hbot hdvd

private theorem weylFin_mem_finiteLevelOne (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    weylFin (ratPrime p) ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  rw [mem_finiteLevelOne_iff]
  exact ⟨weylFin_isLevelOneMatrix p hpN, weylFin_isLevelOneMatrix p hpN⟩

private theorem weylV_mem_U (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hpN : ¬ (p : ℕ) ∣ Ideal.absNorm L) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p)) ∈ h4pins.U L := by
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mpr (weylFin_mem_finiteLevelOne p hpN),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)⟩

end S5SupplyW
section S5SupplyKey
private theorem glArch_heckeGenAt (p : Nat.Primes) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst (pUnit p) i j

private noncomputable def piAdele (p : Nat.Primes) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ)

private theorem piAdele_apply_of_ne {p : Nat.Primes} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ ratPrime p) : piAdele p w = 1 :=
  localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hw

private theorem glFin_heckeGenAt_val (p : Nat.Primes) :
    ((glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![piAdele p, 0; 0, 1] := by
  rw [Matrix.eta_fin_two ((glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
  rfl

private theorem weylGen_entry_LA (p : Nat.Primes) :
    (finCoDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
        + finDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)
      = piAdele p := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finCoDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
      + finDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)) w = piAdele p w
  simp only [coe_add_apply, coe_mul_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw, piAdele_apply_of_ne hw]
    ring

private theorem weylGen_entry_LB (p : Nat.Primes) :
    (finCoDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
        + finDelta (ratPrime p) * finCoDelta (ratPrime p)
      = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finCoDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
      + finDelta (ratPrime p) * finCoDelta (ratPrime p)) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  simp only [coe_add_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]
    ring

private theorem weylGen_entry_LC (p : Nat.Primes) :
    (finDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
        + finCoDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)
      = 0 := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finDelta (ratPrime p) * piAdele p) * (finCoDelta (ratPrime p) * piAdele p)
      + finCoDelta (ratPrime p) * (finDelta (ratPrime p) * piAdele p)) w
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) w
  simp only [coe_add_apply, coe_mul_apply, coe_zero_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw]
    ring

private theorem weylGen_entry_LD (p : Nat.Primes) :
    (finDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
        + finCoDelta (ratPrime p) * finCoDelta (ratPrime p)
      = piAdele p := by
  refine Subtype.ext (funext fun w => ?_)
  show ((finDelta (ratPrime p) * piAdele p) * finDelta (ratPrime p)
      + finCoDelta (ratPrime p) * finCoDelta (ratPrime p)) w = piAdele p w
  simp only [coe_add_apply, coe_mul_apply]
  by_cases hw : w = ratPrime p
  · subst hw
    rw [finCoDelta_apply_self, finDelta_apply_self]
    ring
  · rw [finCoDelta_apply_of_ne hw, finDelta_apply_of_ne hw, piAdele_apply_of_ne hw]
    ring

private theorem weylGen_sq (p : Nat.Primes) :
    (weylFin (ratPrime p) * glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
        * (weylFin (ratPrime p) * glFin (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rw [glFin_heckeGenAt_val,
    show ((weylFin (ratPrime p) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = !![finCoDelta (ratPrime p), finDelta (ratPrime p);
          finDelta (ratPrime p), finCoDelta (ratPrime p)] from rfl,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = Matrix.scalar (Fin 2) (piAdele p) from rfl]
  rw [Matrix.mul_fin_two]
  simp only [mul_zero, add_zero, zero_add, mul_one]
  rw [Matrix.mul_fin_two, weylGen_entry_LA p, weylGen_entry_LB p, weylGen_entry_LC p,
    weylGen_entry_LD p,
    show Matrix.scalar (Fin 2) (piAdele p) = !![piAdele p, 0; 0, piAdele p] from by
      rw [Matrix.eta_fin_two (Matrix.scalar (Fin 2) (piAdele p))]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]]

private theorem central_mul_heckeGenAt_inv_eq_weyl_sandwich (p : Nat.Primes) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))⁻¹
    = AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p))
      * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
      * AdelicDock.finEmbed (𝓞 ℚ) ℚ (weylFin (ratPrime p)) := by
  rw [← finEmbed_scalar_eq_centralScalar]
  refine glpair_ext ?_ ?_
  · rw [map_mul, map_mul, map_mul, map_inv, AdelicDock.glArch_finEmbed,
      AdelicDock.glArch_finEmbed, glArch_heckeGenAt]
    simp
  · rw [map_mul, map_mul, map_mul, map_inv, AdelicDock.glFin_finEmbed,
      AdelicDock.glFin_finEmbed]
    rw [mul_inv_eq_iff_eq_mul, mul_assoc]
    exact (weylGen_sq p).symm

end S5SupplyKey
section S5F4Supply
private theorem glArch_heckeGenAt_unit (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (t : ((v.adicCompletion ℚ))ˣ) :
    glArch (𝓞 ℚ) ℚ (heckeGenAt (𝓞 ℚ) ℚ v t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst t i j

private theorem finComponent_glFin_mem_integralSubgroup
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) {L : Ideal (𝓞 ℚ)}
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hg : g ∈ levelOne (𝓞 ℚ) ℚ L) :
    finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ g)
      ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) := by
  have h := mem_levelOne_iff.mp hg
  have h1 := (mem_finiteLevelOne_iff.mp h).1.integral
  have h2 := (mem_finiteLevelOne_iff.mp h).2.integral
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem
    (IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))]
  refine ⟨fun i j => ⟨⟨_, h1 i j v⟩, rfl⟩, fun i j => ?_⟩
  rw [← map_inv]
  exact ⟨⟨_, h2 i j v⟩, rfl⟩

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

private theorem finComponent_mul_gen_mem_heckeMulSet (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ levelOne (𝓞 ℚ) ℚ L) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
        (u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      ∈ LocalGL2.heckeMulSet (pInt p) (hpInt_ne p) := by
  rw [map_mul, map_mul]
  exact (LocalGL2.mem_heckeMulSet_iff _ _).mpr
    ⟨finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ u),
      finComponent_glFin_mem_integralSubgroup (ratPrime p) hu,
      by rw [finComponent_glFin_heckeGenAt_self]⟩

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

private theorem upperTriQ_uni_mul (b c : ℚ) :
    upperTriQ 1 b 1 one_ne_zero one_ne_zero * upperTriQ 1 c 1 one_ne_zero one_ne_zero
      = upperTriQ 1 (b + c) 1 one_ne_zero one_ne_zero := by
  refine Units.ext ?_
  rw [Units.val_mul]
  show (!![(1 : ℚ), b; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) * !![(1 : ℚ), c; 0, 1]
      = !![(1 : ℚ), b + c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriQ_uni_inv (b : ℚ) :
    (upperTriQ 1 b 1 one_ne_zero one_ne_zero)⁻¹
      = upperTriQ 1 (-b) 1 one_ne_zero one_ne_zero := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [upperTriQ_uni_mul, add_neg_cancel]
  refine Units.ext ?_
  show (!![(1 : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem isLevelOneMatrix_glFin_globalPoints_uniQ (b : ℚ)
    (hb : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (w.adicCompletion ℚ) b ∈ w.adicCompletionIntegers ℚ)
    {L : Ideal (𝓞 ℚ)} :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
  · rw [glFin_globalPoints_apply_place]
    fin_cases i <;> fin_cases j
    · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_one]
      exact one_mem _
    · exact hb w
    · show algebraMap ℚ (w.adicCompletion ℚ) (0 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_zero]
      exact zero_mem _
    · show algebraMap ℚ (w.adicCompletion ℚ) (1 : ℚ) ∈ w.adicCompletionIntegers ℚ
      rw [map_one]
      exact one_mem _
  · rw [show (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0) w
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 w from rfl,
      glFin_globalPoints_apply_place,
      show ((upperTriQ 1 b 1 one_ne_zero one_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) 1 0)
        = (0 : ℚ) from rfl, map_zero, map_zero]
    exact zero_le'
  · rw [show (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
        (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) w
      = finAdeleEval (𝓞 ℚ) ℚ w (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 b 1 one_ne_zero one_ne_zero)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1) from rfl,
      map_sub, map_one, finAdeleEval_apply, glFin_globalPoints_apply_place,
      show ((upperTriQ 1 b 1 one_ne_zero one_ne_zero : Matrix (Fin 2) (Fin 2) ℚ) 1 1)
        = (1 : ℚ) from rfl, map_one, sub_self, map_zero]
    exact zero_le'

private theorem glFin_globalPoints_uniQ_mem_finiteLevelOne (b : ℚ)
    (hb : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (w.adicCompletion ℚ) b ∈ w.adicCompletionIntegers ℚ)
    {L : Ideal (𝓞 ℚ)} :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 b 1 one_ne_zero one_ne_zero))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
  refine mem_finiteLevelOne_iff.mpr ⟨isLevelOneMatrix_glFin_globalPoints_uniQ b hb, ?_⟩
  rw [← map_inv, ← map_inv, upperTriQ_uni_inv]
  exact isLevelOneMatrix_glFin_globalPoints_uniQ (-b)
    (fun w => by rw [map_neg]; exact neg_mem (hb w))

private theorem uniQ_mem_U (n : ℕ) {L : Ideal (𝓞 ℚ)} :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) ∈ h4pins.U L := by
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff _ _ _).mpr
      (glFin_globalPoints_uniQ_mem_finiteLevelOne _
        (fun w => by rw [map_neg]; exact neg_mem (natInt w n).2)),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _)⟩

private theorem finComponent_glFin_globalPoints_uniQ_self (p : Nat.Primes) (n : ℕ) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
      = LocalGL2.unipotentInt ((ratPrime p).adicCompletion ℚ)
          (-(natInt (ratPrime p) n)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [show ((finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
      (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))) :
      Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ)) i j)
      = ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (upperTriQ 1 (-((n : ℕ) : ℚ)) 1
          one_ne_zero one_ne_zero)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
        (ratPrime p) from rfl,
    glFin_globalPoints_apply_place]
  fin_cases i <;> fin_cases j
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (1 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_one, map_one]
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (-((n : ℕ) : ℚ))
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (-(natInt (ratPrime p) n))
    rw [map_neg, map_neg]
    rfl
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (0 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (0 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_zero, map_zero]
  · show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (1 : ℚ)
      = algebraMap ((ratPrime p).adicCompletionIntegers ℚ) ((ratPrime p).adicCompletion ℚ)
          (1 : (ratPrime p).adicCompletionIntegers ℚ)
    rw [map_one, map_one]

private theorem finComponent_glFin_repsFin_self (p : Nat.Primes) (n : ℕ) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
        * heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
      = LocalGL2.localRepSome (pInt p) (hpInt_ne p) (-(natInt (ratPrime p) n)) := by
  rw [map_mul, map_mul, AdelicDock.glFin_finEmbed, finComponent_glFin_heckeGenAt_self,
    finComponent_glFin_globalPoints_uniQ_self]
  rfl

private theorem isLevelOneMatrix_of_eq_off_of_integral_at
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ v.asIdeal ∣ L)
    {Z Y : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hY : IsLevelOneMatrix (𝓞 ℚ) ℚ L (Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      finComponent (𝓞 ℚ) ℚ w Z = finComponent (𝓞 ℚ) ℚ w Y)
    (hat : finComponent (𝓞 ℚ) ℚ v Z
      ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ L (Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hent : ∀ (i j : Fin 2) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)), w ≠ v →
      ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w
        = ((Y : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) w :=
    fun i j w hw => congrArg (fun u : GL (Fin 2) (w.adicCompletion ℚ) =>
      (u : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j) (hoff w hw)
  have hatv : ∀ i j : Fin 2,
      ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v
        ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hat i j
    rw [show ((Z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) v
        = (finComponent (𝓞 ℚ) ℚ v Z :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j from rfl, ← hr]
    exact r.2
  have hsub : ∀ (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
      ((M 1 1 - 1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w = (M 1 1) w - 1 := fun M w => by
    rw [show ((M 1 1 - 1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) w
        = finAdeleEval (𝓞 ℚ) ℚ w (M 1 1 - 1) from rfl, map_sub, map_one, finAdeleEval_apply]
  refine ⟨⟨fun i j => fun w => ?_, fun w => ?_⟩, fun w => ?_⟩
  · by_cases hw : w = v
    · subst hw; exact hatv i j
    · rw [hent i j w hw]; exact hY.integral i j w
  · by_cases hw : w = v
    · subst hw
      rw [idealBound_eq_one_of_not_dvd hLbot hvL]
      exact (mem_adicCompletionIntegers _ _ _).mp (hatv 1 0)
    · rw [hent 1 0 w hw]; exact hY.lowerLeft w
  · by_cases hw : w = v
    · subst hw
      rw [hsub, idealBound_eq_one_of_not_dvd hLbot hvL]
      exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hatv 1 1) (one_mem _))
    · rw [hsub, hent 1 1 w hw, ← hsub]; exact hY.lowerRight w

private theorem finComponent_glFin_central_of_ne (p : Nat.Primes)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ ratPrime p) :
    finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ
      (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2) w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    show ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1
    exact localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) hw
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    show ((0 : AdeleRing (𝓞 ℚ) ℚ).2) w = 0
    rfl

private theorem finComponent_glFin_central_self_val (p : Nat.Primes) :
    (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))))) :
        Matrix (Fin 2) (Fin 2) ((ratPrime p).adicCompletion ℚ))
      = !![(pUnit p : (ratPrime p).adicCompletion ℚ), 0;
          0, (pUnit p : (ratPrime p).adicCompletion ℚ)] := by
  ext i j : 1
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).2) (ratPrime p) = _
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    have : ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) (ratPrime p) = (pUnit p : (ratPrime p).adicCompletion ℚ) :=
      localUnit_apply_self (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)
    rw [show ((((Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) :
        (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl, this]
    fin_cases i <;> rfl
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    have h0 : ((0 : AdeleRing (𝓞 ℚ) ℚ).2) (ratPrime p)
        = (0 : (ratPrime p).adicCompletion ℚ) := rfl
    rw [h0]
    fin_cases i <;> fin_cases j <;> simp_all

private theorem glArch_central (p : Nat.Primes) :
    glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  show ((Matrix.scalar (Fin 2) (((Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        AdeleRing (𝓞 ℚ) ℚ)) i j).1) = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact finIncl_apply_fst (𝓞 ℚ) ℚ _
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rfl

private theorem finComponent_glFin_repsLast_self (p : Nat.Primes) :
    finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ
      (centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
          (localUnit (𝓞 ℚ) ℚ (ratPrime p) (pUnit p)))
        * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (pUnit p))⁻¹))
      = LocalGL2.localRepInf (pInt p) (hpInt_ne p) := by
  rw [map_mul, map_mul, map_inv, map_inv, finComponent_glFin_heckeGenAt_self]
  refine Units.ext ?_
  rw [Units.val_mul, finComponent_glFin_central_self_val, LocalGL2.coe_diagPi_inv,
    LocalGL2.coe_localRepInf,
    show (algebraMap ((ratPrime p).adicCompletionIntegers ℚ)
        ((ratPrime p).adicCompletion ℚ) (pInt p))
      = (pUnit p : (ratPrime p).adicCompletion ℚ) from rfl,
    Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add,
    mul_inv_cancel₀ (pUnit p).ne_zero]

private theorem mem_U_of_arch_off_at (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ (ratPrime p).asIdeal ∣ L)
    {T y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : y ∈ h4pins.U L)
    (harch : glArch (𝓞 ℚ) ℚ T = 1)
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ ratPrime p →
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ T) = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ y))
    (hat : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ T)
      ∈ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
          ((ratPrime p).adicCompletion ℚ)) :
    T ∈ h4pins.U L := by
  have hyL : glFin (𝓞 ℚ) ℚ y ∈ finiteLevelOne (𝓞 ℚ) ℚ L := by
    rw [productionPinsCompact_U, Subgroup.mem_inf] at hy
    exact mem_levelOne_iff.mp hy.1
  rw [productionPinsCompact_U, Subgroup.mem_inf]
  refine ⟨mem_levelOne_iff.mpr (mem_finiteLevelOne_iff.mpr ⟨?_, ?_⟩),
    (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr harch⟩
  · exact isLevelOneMatrix_of_eq_off_of_integral_at (ratPrime p) hLbot hvL
      (mem_finiteLevelOne_iff.mp hyL).1 hoff hat
  · refine isLevelOneMatrix_of_eq_off_of_integral_at (ratPrime p) hLbot hvL
      (mem_finiteLevelOne_iff.mp hyL).2 (fun w hw => ?_) ?_
    · simp only [map_inv]
      rw [hoff w hw]
    · rw [map_inv]
      exact inv_mem hat

private theorem mk_eq_mk_of_transfer (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    (hLbot : L ≠ ⊥) (hvL : ¬ (ratPrime p).asIdeal ∣ L)
    {z r y : AdelicGL2 (𝓞 ℚ) ℚ} (hy : y ∈ h4pins.U L)
    (harch : glArch (𝓞 ℚ) ℚ (z⁻¹ * r) = 1)
    (hoff : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w ≠ ratPrime p →
      finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (z⁻¹ * r))
        = finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ y))
    (hat : (QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ z)) :
          _ ⧸ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
            ((ratPrime p).adicCompletion ℚ))
        = QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ r))) :
    (QuotientGroup.mk z : _ ⧸ h4pins.U L) = QuotientGroup.mk r := by
  refine QuotientGroup.eq.mpr (mem_U_of_arch_off_at p hLbot hvL hy harch hoff ?_)
  have h2 := QuotientGroup.eq.mp hat
  have he : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (z⁻¹ * r))
      = (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ z))⁻¹
        * finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ r) := by
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [he]
  exact h2

private theorem mk_loc_eq_of_mk_eq (p : Nat.Primes) {L : Ideal (𝓞 ℚ)}
    {a b : AdelicGL2 (𝓞 ℚ) ℚ}
    (h : (QuotientGroup.mk a : _ ⧸ h4pins.U L) = QuotientGroup.mk b) :
    (QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ a)) :
        _ ⧸ LocalGL2.integralSubgroup ((ratPrime p).adicCompletionIntegers ℚ)
          ((ratPrime p).adicCompletion ℚ))
      = QuotientGroup.mk (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ b)) := by
  have hmem := QuotientGroup.eq.mp h
  have hL : a⁻¹ * b ∈ levelOne (𝓞 ℚ) ℚ L := by
    rw [productionPinsCompact_U, Subgroup.mem_inf] at hmem
    exact hmem.1
  have hint := finComponent_glFin_mem_integralSubgroup (ratPrime p) hL
  refine QuotientGroup.eq.mpr ?_
  have he : finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ (a⁻¹ * b))
      = (finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ a))⁻¹
        * finComponent (𝓞 ℚ) ℚ (ratPrime p) (glFin (𝓞 ℚ) ℚ b) := by
    rw [map_mul, map_mul, map_inv, map_inv]
  rw [← he]
  exact hint

private theorem pInt_not_dvd_natInt_sub (p : Nat.Primes) {a b : ℕ}
    (ha : a < (p : ℕ)) (hba : b < a) :
    ¬ pInt p ∣ (natInt (ratPrime p) a - natInt (ratPrime p) b) := by
  intro hdvd
  have hsub : natInt (ratPrime p) a - natInt (ratPrime p) b
      = natInt (ratPrime p) (a - b) := by
    refine Subtype.ext ?_
    show algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((a : ℕ) : ℚ)
        - algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((b : ℕ) : ℚ)
      = algebraMap ℚ ((ratPrime p).adicCompletion ℚ) (((a - b : ℕ) : ℚ))
    rw [← map_sub]
    congr 1
    rw [Nat.cast_sub hba.le]
  rw [hsub] at hdvd
  have hunit := isUnit_natInt_of_not_dvd p
    (n := a - b) (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have h1 := valued_eq_one_of_isUnit hunit
  obtain ⟨c, hc⟩ := hdvd
  rw [hc] at h1
  have h2 : Valued.v (((pInt p * c : (ratPrime p).adicCompletionIntegers ℚ))
      : (ratPrime p).adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
    rw [show (((pInt p * c : (ratPrime p).adicCompletionIntegers ℚ))
        : (ratPrime p).adicCompletion ℚ)
        = ((pInt p : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ)
          * ((c : (ratPrime p).adicCompletionIntegers ℚ)
            : (ratPrime p).adicCompletion ℚ) from rfl,
      Valuation.map_mul, valued_pInt]
    calc WithZero.exp (-1 : ℤ) * Valued.v ((c : (ratPrime p).adicCompletionIntegers ℚ)
          : (ratPrime p).adicCompletion ℚ)
        ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl (valued_adicInt_le_one c)
      _ = WithZero.exp (-1 : ℤ) := mul_one _
  rw [h1, ← WithZero.exp_zero] at h2
  have := withZero_exp_le_exp.mp h2
  omega

end S5F4Supply
section H7Heads
private theorem isHeckeCosetSystem_heckeReps (p : ℕ) (hp : p.Prime)
    (L : Ideal (𝓞 ℚ)) (hpN : ¬ p ∣ Ideal.absNorm L) :
    HeckeIntegralSeam.IsHeckeCosetSystem (h4pins.U L)
      (h4pins.gen (ratPrime ⟨p, hp⟩)) (heckeReps p hp) := by
  obtain ⟨hvL, hLbot⟩ := ratPrime_not_dvd_of_not_dvd_absNorm ⟨p, hp⟩ hpN
  have hAN : Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal = p := by rw [absNorm_ratPrime]
  have hpc : ((⟨p, hp⟩ : Nat.Primes) : ℕ) = p := rfl
  have hseam : (h4pins.gen (ratPrime ⟨p, hp⟩))⁻¹
      * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) ∈ h4pins.U L := by
    rw [productionPinsCompact_U, productionPinsCompact_gen, Subgroup.mem_inf]
    have harch : glArch (𝓞 ℚ) ℚ (heckeGen (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩)) = 1 :=
      glArch_heckeGenAt_unit (ratPrime ⟨p, hp⟩) (uniformizerUnit ℚ (ratPrime ⟨p, hp⟩))
    refine ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne _ (valued_pUnit ⟨p, hp⟩) L, ?_⟩
    refine (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr ?_
    rw [map_mul, map_inv, harch, glArch_heckeGenAt_unit, inv_one, one_mul]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i
    by_cases hi : (i : ℕ) < p
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
        simp only [heckeReps]; rw [if_pos hi]]
      exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨_, uniQ_mem_U (i : ℕ), _, hseam, by group⟩
    · rw [show heckeReps p hp i
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
        simp only [heckeReps]; rw [if_neg hi],
        central_mul_heckeGenAt_inv_eq_weyl_sandwich ⟨p, hp⟩]
      exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨_, weylV_mem_U ⟨p, hp⟩ hpN, _, mul_mem hseam (weylV_mem_U ⟨p, hp⟩ hpN), by group⟩
  ·
    intro x hx
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have huL : u ∈ levelOne (𝓞 ℚ) ℚ L := by
      rw [productionPinsCompact_U, Subgroup.mem_inf] at hu
      exact hu.1
    have huA : glArch (𝓞 ℚ) ℚ u = 1 := by
      rw [productionPinsCompact_U, Subgroup.mem_inf] at hu
      exact (mem_finiteAdelicGL2Subgroup_iff ℚ _).mp hu.2
    have hg0 : u * h4pins.gen (ratPrime ⟨p, hp⟩)
          * ((h4pins.gen (ratPrime ⟨p, hp⟩))⁻¹
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))
        = u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) := by group
    have hmkz : (QuotientGroup.mk (u * h4pins.gen (ratPrime ⟨p, hp⟩) * u')
          : _ ⧸ h4pins.U L)
        = QuotientGroup.mk (u * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)) := by
      rw [QuotientGroup.mk_mul_of_mem _ hu', ← hg0, QuotientGroup.mk_mul_of_mem _ hseam]
    have hmul := finComponent_mul_gen_mem_heckeMulSet ⟨p, hp⟩ huL
    rcases LocalGL2.exists_rep_of_mem_heckeMulSet (pInt ⟨p, hp⟩) (hpInt_ne ⟨p, hp⟩)
        (irreducible_pInt ⟨p, hp⟩) hmul with ⟨b, hb⟩ | hinf
    ·
      obtain ⟨n, hn, hdvd⟩ := exists_natInt_dvd_sub ⟨p, hp⟩ (-b)
      have hdvd' : pInt ⟨p, hp⟩ ∣ b - -(natInt (ratPrime ⟨p, hp⟩) n) := by
        have h2 : pInt ⟨p, hp⟩ ∣ -(-b - natInt (ratPrime ⟨p, hp⟩) n) := dvd_neg.mpr hdvd
        have h3 : -(-b - natInt (ratPrime ⟨p, hp⟩) n)
            = b - -(natInt (ratPrime ⟨p, hp⟩) n) := by ring
        rwa [h3] at h2
      refine ⟨⟨n, by omega⟩, ?_⟩
      rw [show heckeReps p hp ⟨n, by omega⟩
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
        simp only [heckeReps]; rw [if_pos (show ((⟨n, by omega⟩ :
          Fin (Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1)) : ℕ) < p from hn)]]
      refine hmkz.trans (mk_eq_mk_of_transfer ⟨p, hp⟩ hLbot hvL
        (y := u⁻¹ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
            (upperTriQ 1 (-((n : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero))))
        (mul_mem (inv_mem hu) (uniQ_mem_U n)) ?_ ?_ ?_)
      · simp only [map_mul, map_inv, huA, AdelicDock.glArch_finEmbed,
          glArch_heckeGenAt_unit, inv_one, mul_one]
      · intro w hw
        simp only [map_mul, map_inv, finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
          mul_one]
      · rw [finComponent_glFin_repsFin_self]
        exact hb.symm.trans (LocalGL2.mk_localRepSome_eq_of_dvd_sub _ _ hdvd').symm
    ·
      refine ⟨⟨p, by omega⟩, ?_⟩
      rw [show heckeReps p hp ⟨p, by omega⟩
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
        simp only [heckeReps]; rw [if_neg (lt_irrefl p)]]
      refine hmkz.trans (mk_eq_mk_of_transfer ⟨p, hp⟩ hLbot hvL
        (y := u⁻¹) (inv_mem hu) ?_ ?_ ?_)
      · simp only [map_mul, map_inv, huA, glArch_central ⟨p, hp⟩,
          glArch_heckeGenAt_unit, inv_one, mul_one]
      · intro w hw
        simp only [map_mul, map_inv, finComponent_glFin_heckeGenAt_of_ne ⟨p, hp⟩ hw,
          finComponent_glFin_central_of_ne ⟨p, hp⟩ hw, inv_one, mul_one]
      · rw [finComponent_glFin_repsLast_self]
        exact hinf.symm
  ·
    intro i j hij
    have hloc := mk_loc_eq_of_mk_eq ⟨p, hp⟩ hij
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hi],
        show heckeReps p hp j
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((j : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hj],
        finComponent_glFin_repsFin_self, finComponent_glFin_repsFin_self] at hloc
      have hdvd := LocalGL2.dvd_sub_of_mk_localRepSome_eq _ _ hloc
      have hsub2 : (-(natInt (ratPrime ⟨p, hp⟩) (j : ℕ))
            - -(natInt (ratPrime ⟨p, hp⟩) (i : ℕ)))
          = natInt (ratPrime ⟨p, hp⟩) (i : ℕ) - natInt (ratPrime ⟨p, hp⟩) (j : ℕ) := by
        ring
      rw [hsub2] at hdvd
      by_contra hne
      have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact pInt_not_dvd_natInt_sub ⟨p, hp⟩ hj h (dvd_sub_comm.mp hdvd)
      · exact pInt_not_dvd_natInt_sub ⟨p, hp⟩ hi h hdvd
    · rw [show heckeReps p hp i
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hi],
        show heckeReps p hp j
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
          simp only [heckeReps]; rw [if_neg hj],
        finComponent_glFin_repsFin_self, finComponent_glFin_repsLast_self] at hloc
      exact absurd hloc (LocalGL2.mk_localRepSome_ne_mk_localRepInf _ _
        (irreducible_pInt ⟨p, hp⟩).not_isUnit _)
    · rw [show heckeReps p hp i
          = centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ)
              (localUnit (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩)))
            * (heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩))⁻¹ from by
          simp only [heckeReps]; rw [if_neg hi],
        show heckeReps p hp j
          = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperTriQ 1 (-((j : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ (ratPrime ⟨p, hp⟩) (pUnit ⟨p, hp⟩) from by
          simp only [heckeReps]; rw [if_pos hj],
        finComponent_glFin_repsLast_self, finComponent_glFin_repsFin_self] at hloc
      exact absurd hloc.symm (LocalGL2.mk_localRepSome_ne_mk_localRepInf _ _
        (irreducible_pInt ⟨p, hp⟩).not_isUnit _)
    · have hi2 := i.isLt
      have hj2 := j.isLt
      exact Fin.ext (by omega)

end H7Heads
end AdelicDescentHE
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.AdelicDescentHE"
end
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.AdelicDescentHE"
end Part06
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.AdelicDescentHE"

namespace AdelicDescentHE

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι κ : Type*} {reps : ι → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps)
    (e : κ ≃ ι) : HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective (by simpa using hkk'))

theorem pUnit_eq_of_val_eq (p : Nat.Primes) (ϖ : ((ratPrime p).adicCompletion ℚ)ˣ)
    (hϖ : (ϖ : (ratPrime p).adicCompletion ℚ) = algebraMap ℚ _ ((p : ℕ) : ℚ)) :
    ϖ = pUnit p := Units.ext hϖ

end AdelicDescentHE
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.AdelicDescentHE"

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SiegelCoordinates IsDedekindDomain AdelicDescentHE in

theorem solution
    (L : Ideal (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ Ideal.absNorm L)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ v)
      (fun i : Fin (p + 1) =>
        if (i : ℕ) < p then
          AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperUnit (1 : ℚ) (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ v ϖ
        else
          centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ))
            * (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹) := by
  obtain rfl : v = ratPrime ⟨p, hp⟩ := eq_ratPrime_of_natCast_mem ⟨p, hp⟩ hv
  obtain rfl : ϖ = pUnit ⟨p, hp⟩ := pUnit_eq_of_val_eq ⟨p, hp⟩ ϖ hϖ
  have habs : Ideal.absNorm (ratPrime ⟨p, hp⟩).asIdeal + 1 = p + 1 := by
    rw [absNorm_ratPrime]
  have hsys := isHeckeCosetSystem_comp_equiv
    (isHeckeCosetSystem_heckeReps p hp L hpL) (finCongr habs.symm)
  convert hsys using 1 <;> rfl

end S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
end P2MW
export P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm (solution)
