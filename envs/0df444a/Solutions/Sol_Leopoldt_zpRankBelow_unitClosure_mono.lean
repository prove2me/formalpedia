-- Prove2me | solution 1 for Leopoldt.zpRankBelow_unitClosure_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T15:22:54.405744+00:00
-- url     : https://prove2.me/submissions/4e721cf7-8f99-4956-b01b-ffe30b470c9c

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain

/-!
Functoriality of the semilocal units at `p` along a finite extension of number fields, and the
resulting monotonicity of the `ℤ_p`-rank of the `p`-adic closure of the global units.
-/

namespace LeopoldtMono

section Local

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The coercion `WithVal (w.valuation K) →+* w.adicCompletion K` as a ring hom. -/
noncomputable def coeHom : WithVal (w.valuation K) →+* w.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.equiv K w).symm.toRingHom.comp
    UniformSpace.Completion.coeRingHom

theorem continuous_coeHom : Continuous (coeHom (K := K) w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
    UniformSpace.Completion.continuous_coeRingHom

/-- `F → w.adicCompletion K`, as a ring hom on the `v`-valued copy of `F`. -/
noncomputable def coeAlgHom : WithVal (v.valuation F) →+* w.adicCompletion K :=
  (coeHom (K := K) w).comp (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation K)))

theorem continuous_coeAlgHom : Continuous (coeAlgHom v w) :=
  (continuous_coeHom w).comp
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F K v w).continuous

/-- The map on adic completions induced by `K/F`, for `w` lying over `v`. -/
noncomputable def compHom : v.adicCompletion F →+* w.adicCompletion K :=
  (UniformSpace.Completion.extensionHom (coeAlgHom v w) (continuous_coeAlgHom v w)).comp
    (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom

theorem continuous_compHom : Continuous (compHom v w) :=
  UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v)

theorem compHom_coe (x : F) :
    compHom v w ((x : F) : v.adicCompletion F) = ((algebraMap F K x : K) : w.adicCompletion K) := by
  show UniformSpace.Completion.extensionHom (coeAlgHom v w) (continuous_coeAlgHom v w)
      (((WithVal.equiv (v.valuation F)).symm x : WithVal (v.valuation F)) :
        (v.valuation F).Completion) = _
  rw [UniformSpace.Completion.extensionHom_coe]
  rfl

theorem algebraMap_eq_coe (x : F) :
    algebraMap F (v.adicCompletion F) x = ((x : F) : v.adicCompletion F) := rfl

theorem valued_compHom_coe (x : F) :
    Valued.v (compHom v w ((x : F) : v.adicCompletion F))
      = (v.valuation F x) ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  rw [compHom_coe, HeightOneSpectrum.adicCompletion.valued_coe,
    ← HeightOneSpectrum.valuation_liesOver K v w x]

theorem compHom_mem (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) :
    compHom v w y ∈ w.adicCompletionIntegers K := by
  have hS : IsClosed {z : v.adicCompletion F | Valued.v (compHom v w z) ≤ 1} :=
    (Valued.isClosed_integer (w.adicCompletion K)).preimage (continuous_compHom v w)
  have hA : IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isOpen_integer (v.adicCompletion F)
  have hkey : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∩
      Set.range (algebraMap F (v.adicCompletion F)) ⊆
      {z : v.adicCompletion F | Valued.v (compHom v w z) ≤ 1} := by
    rintro z ⟨hz, x, rfl⟩
    have hz' : Valued.v (((x : F)) : v.adicCompletion F) ≤ 1 := by
      rw [algebraMap_eq_coe] at hz; exact hz
    rw [HeightOneSpectrum.adicCompletion.valued_coe] at hz'
    show Valued.v (compHom v w (algebraMap F (v.adicCompletion F) x)) ≤ 1
    rw [algebraMap_eq_coe, valued_compHom_coe]
    exact Right.pow_le_one_of_le hz'
  exact hS.closure_subset_iff.mpr hkey
    ((HeightOneSpectrum.denseRange_algebraMap F v).open_subset_closure_inter hA hy)

/-- The induced map on the rings of integers of the completions. -/
noncomputable def compIntHom :
    v.adicCompletionIntegers F →+* w.adicCompletionIntegers K :=
  RingHom.codRestrict ((compHom v w).comp (v.adicCompletionIntegers F).subtype)
    (w.adicCompletionIntegers K) (fun x => compHom_mem v w x x.2)

theorem coe_compIntHom (x : v.adicCompletionIntegers F) :
    ((compIntHom v w x : w.adicCompletionIntegers K) : w.adicCompletion K)
      = compHom v w (x : v.adicCompletion F) := rfl

theorem continuous_compIntHom : Continuous (compIntHom v w) :=
  continuous_induced_rng.2 ((continuous_compHom v w).comp continuous_subtype_val)

theorem compIntHom_injective : Function.Injective (compIntHom v w) := by
  intro a b hab
  exact Subtype.ext ((compHom v w).injective (congrArg Subtype.val hab))

/-- The induced map on the local unit groups. -/
noncomputable def unitHom :
    (v.adicCompletionIntegers F)ˣ →* (w.adicCompletionIntegers K)ˣ :=
  Units.map (compIntHom v w).toMonoidHom

theorem unitHom_injective : Function.Injective (unitHom v w) := fun _ _ hab =>
  Units.ext (compIntHom_injective v w (congrArg Units.val hab))

theorem continuous_unitHom : Continuous (unitHom v w) := by
  rw [Units.continuous_iff]
  exact ⟨(continuous_compIntHom v w).comp Units.continuous_val,
    (continuous_compIntHom v w).comp (Units.continuous_val.comp continuous_inv)⟩

end Local

section Global

open Leopoldt

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  {K : Type*} [Field K] [NumberField K] [Algebra F K]

/-- The prime of `𝓞 F` below a prime of `𝓞 K` above `p`. -/
def primeBelow (w : PrimesOver p K) : PrimesOver p F := by
  refine ⟨⟨w.1.asIdeal.under (𝓞 F), Ideal.IsPrime.under (𝓞 F) w.1.asIdeal, ?_⟩, ?_⟩
  · intro h
    have hp : (p : 𝓞 F) ∈ w.1.asIdeal.under (𝓞 F) := by
      simpa [Ideal.under, Ideal.mem_comap] using w.2
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out (p := p.Prime)).ne_zero) hp
  · simpa [Ideal.under, Ideal.mem_comap] using w.2

instance liesOver_primeBelow (w : PrimesOver p K) :
    (w.1.asIdeal).LiesOver (primeBelow p F w).1.asIdeal := ⟨rfl⟩

theorem primeBelow_surjective : Function.Surjective (primeBelow p F (K := K)) := by
  intro v
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := 𝓞 F) (S := 𝓞 K)
    v.1.asIdeal ⊥ (by simp)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply v.1.ne_bot
    rw [← hQc, h]
    simp [Ideal.comap_bot_of_injective (algebraMap (𝓞 F) (𝓞 K))
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have h : (p : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) Q := by rw [hQc]; exact v.2
    simpa [Ideal.mem_comap] using h
  refine ⟨⟨⟨Q, hQp, hQ0⟩, hpQ⟩, ?_⟩
  exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext hQc)

/-- The induced map on semilocal units. -/
noncomputable def semilocalHom : SemilocalUnits p F →* SemilocalUnits p K :=
  MonoidHom.pi fun w => (unitHom (primeBelow p F w).1 w.1).comp
    (Pi.evalMonoidHom (fun v : PrimesOver p F => (v.1.adicCompletionIntegers F)ˣ)
      (primeBelow p F w))

theorem semilocalHom_apply (x : SemilocalUnits p F) (w : PrimesOver p K) :
    semilocalHom p F x w = unitHom (primeBelow p F w).1 w.1 (x (primeBelow p F w)) := rfl

theorem continuous_semilocalHom : Continuous (semilocalHom p F (K := K)) :=
  continuous_pi fun w => (continuous_unitHom _ _).comp (continuous_apply _)

theorem semilocalHom_injective : Function.Injective (semilocalHom p F (K := K)) := by
  intro x y hxy
  funext v
  obtain ⟨w, rfl⟩ := primeBelow_surjective p F (K := K) v
  exact unitHom_injective _ _ (congrFun hxy w)

theorem compHom_algebraMap_int {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)}
    [w.asIdeal.LiesOver v.asIdeal] (a : 𝓞 F) :
    compHom v w ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F))
      = ((algebraMap (𝓞 K) (w.adicCompletionIntegers K)
          (algebraMap (𝓞 F) (𝓞 K) a) : w.adicCompletionIntegers K) : w.adicCompletion K) := by
  show compHom v w (((algebraMap (𝓞 F) F a : F)) : v.adicCompletion F) = _
  rw [compHom_coe, ← IsScalarTower.algebraMap_apply (𝓞 F) F K,
    IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K]
  rfl

theorem semilocalHom_diagonalUnits (ε : (𝓞 F)ˣ) :
    semilocalHom p F (diagonalUnits p F ε)
      = diagonalUnits p K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom ε) := by
  funext w
  exact Units.ext (Subtype.ext (compHom_algebraMap_int F ε.val))

theorem semilocalHom_mem_unitClosure {x : SemilocalUnits p F} (hx : x ∈ unitClosure p F) :
    semilocalHom p F (K := K) x ∈ unitClosure p K := by
  simp only [unitClosure, Subgroup.mem_iInf] at hx ⊢
  intro n
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hx n)
  obtain ⟨ε, hε⟩ := ha
  obtain ⟨u, hu⟩ := hb
  refine Subgroup.mem_sup.2
    ⟨diagonalUnits p K (Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom ε), ⟨_, rfl⟩,
      powMonoidHom (p ^ (n + 1)) (semilocalHom p F u), ⟨_, rfl⟩, ?_⟩
  rw [← semilocalHom_diagonalUnits p F ε]
  show semilocalHom p F (diagonalUnits p F ε) * (semilocalHom p F u) ^ (p ^ (n + 1)) = _
  rw [← map_pow, ← map_mul]
  show semilocalHom p F (diagonalUnits p F ε * powMonoidHom (p ^ (n + 1)) u) = _
  rw [hε, hu, hab]

theorem zero_mem_zpRankSet {G : Type*} [CommGroup G] [TopologicalSpace G]
    (bound : ℕ) (H : Subgroup G) :
    (0 : ℕ) ∈ {n : ℕ | n ≤ bound ∧ ∃ f : Multiplicative (Fin n → ℤ_[p]) →* G,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ H} := by
  refine ⟨Nat.zero_le _, 1, ?_, continuous_const, fun _ => H.one_mem⟩
  intro a b _
  have h : (Multiplicative.toAdd a) = (Multiplicative.toAdd b) := by
    funext i; exact i.elim0
  simpa using h

theorem finrank_le [FiniteDimensional F K] : Module.finrank ℚ F ≤ Module.finrank ℚ K := by
  have h := Module.finrank_mul_finrank ℚ F K
  nlinarith [Module.finrank_pos (R := F) (M := K), Module.finrank_pos (R := ℚ) (M := F)]

theorem zpRankBelow_unitClosure_mono [FiniteDimensional F K] :
    zpRankBelow p (Module.finrank ℚ F) (unitClosure p F)
      ≤ zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) := by
  simp only [zpRankBelow]
  refine csSup_le ⟨0, zero_mem_zpRankSet p _ _⟩ ?_
  rintro n ⟨hn, f, hinj, hcont, hmem⟩
  refine le_csSup ⟨Module.finrank ℚ K, fun m hm => hm.1⟩ ⟨hn.trans (finrank_le F),
    (semilocalHom p F).comp f, ?_, ?_, fun x => semilocalHom_mem_unitClosure p F (hmem x)⟩
  · exact (semilocalHom_injective p F).comp hinj
  · exact (continuous_semilocalHom p F).comp hcont

end Global

end LeopoldtMono

/-- The `ℤ_p`-rank of the `p`-adic closure of the global units does not decrease along a finite
extension of number fields. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] :
    Leopoldt.zpRankBelow p (Module.finrank ℚ F) (Leopoldt.unitClosure p F)
      ≤ Leopoldt.zpRankBelow p (Module.finrank ℚ K) (Leopoldt.unitClosure p K) :=
  LeopoldtMono.zpRankBelow_unitClosure_mono p F
