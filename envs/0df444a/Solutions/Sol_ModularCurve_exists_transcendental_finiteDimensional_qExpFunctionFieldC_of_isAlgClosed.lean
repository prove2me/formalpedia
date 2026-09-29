-- Prove2me | solution 1 for ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/385c718f-18c8-5062-9e95-a69c87c7f076

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace QExpBaseChange

open ModularCurve IntermediateField Polynomial

section Transfer

variable {κ k : Type*} [Field κ] [Field k] (φ : κ →+* k)

abbrev Φ : LaurentSeries κ →+* LaurentSeries k := coeffMap φ

theorem Φ_injective : Function.Injective (Φ φ) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries k => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact φ.injective h1

theorem Φ_ne_zero_iff (x : LaurentSeries κ) : Φ φ x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (Φ φ), (Φ_injective φ).eq_iff]

theorem Φ_intSeriesC (p : PowerSeries ℤ) : Φ φ (intSeriesC κ p) = intSeriesC k p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem algebraMap_laurentSeries_eq_C {K : Type*} [Field K] (a : K) :
    algebraMap K (LaurentSeries K) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap K (PowerSeries K) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem Φ_algebraMap (a : κ) :
    Φ φ (algebraMap κ (LaurentSeries κ) a) = algebraMap k (LaurentSeries k) (φ a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffMap_single]

theorem coe_mem_adjoin_of_mem_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) (x : F) {y : F} (hy : y ∈ adjoin K ({x} : Set F)) :
    (y : L) ∈ adjoin K ({(x : L)} : Set L) := by
  have h : (y : L) ∈ (adjoin K ({x} : Set F)).map F.val := ⟨y, hy, rfl⟩
  rwa [adjoin_map, Set.image_singleton] at h

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem image_intFormRatiosC : (Φ φ) '' intFormRatiosC κ Γ = intFormRatiosC k Γ := by
  ext z
  constructor
  · rintro ⟨y, ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨w, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← Φ_intSeriesC φ]; exact (Φ_ne_zero_iff φ _).mpr hg0
    · rw [map_div₀, Φ_intSeriesC, Φ_intSeriesC]
  · rintro ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC κ pf / intSeriesC κ pg, ⟨w, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · rw [← Φ_ne_zero_iff φ, Φ_intSeriesC]; exact hg0
    · rw [map_div₀, Φ_intSeriesC, Φ_intSeriesC]

variable {Γ}

theorem map_mem_adjoin {S : Set (LaurentSeries κ)} {y : LaurentSeries κ} (hy : y ∈ adjoin κ S) :
    Φ φ y ∈ adjoin k ((Φ φ) '' S) := by
  have hy' : y ∈ (adjoin κ S).toSubfield := hy
  rw [adjoin_toSubfield] at hy'
  have hle : Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ S) ≤
      (adjoin k ((Φ φ) '' S)).toSubfield.comap (Φ φ) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · change Φ φ (algebraMap κ (LaurentSeries κ) a) ∈ adjoin k ((Φ φ) '' S)
      rw [Φ_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · change Φ φ z ∈ adjoin k ((Φ φ) '' S)
      exact subset_adjoin k _ ⟨z, hz, rfl⟩
  exact hle hy'

theorem map_mem_qExpFunctionFieldC {y : LaurentSeries κ} (hy : y ∈ qExpFunctionFieldC κ Γ) :
    Φ φ y ∈ qExpFunctionFieldC k Γ := by
  have h := map_mem_adjoin φ hy
  rwa [image_intFormRatiosC] at h

variable (Γ)

local notation "Fκ" => qExpFunctionFieldC κ Γ
local notation "Fk" => qExpFunctionFieldC k Γ

include φ in

theorem transfer (x : Fκ) (hx : (x : LaurentSeries κ) = jqModC κ)
    (hfd : FiniteDimensional (adjoin κ ({x} : Set Fκ)) Fκ) :
    ∃ x' : Fk, (x' : LaurentSeries k) = jqModC k ∧ Transcendental k x' ∧
      FiniteDimensional (adjoin k ({x'} : Set Fk)) Fk := by
  classical

  have hjk : jqModC k ∈ Fk := intFormRatiosC_subset k Γ (ModularCurve.jqModC_mem_intFormRatiosC k Γ)
  let x' : Fk := ⟨jqModC k, hjk⟩
  have hx' : (x' : LaurentSeries k) = jqModC k := rfl
  have hΦx : Φ φ (x : LaurentSeries κ) = jqModC k := by rw [hx, coeffMap_jqModC]
  refine ⟨x', hx', ?_, ?_⟩
  · exact fun h => transcendental_jqModC k
      ((isAlgebraic_algHom_iff (qExpFunctionFieldC k Γ).val Subtype.val_injective).mpr h)

  set Lκ : IntermediateField κ Fκ := adjoin κ ({x} : Set Fκ) with hLκ
  set K₀ : IntermediateField k Fk := adjoin k ({x'} : Set Fk) with hK₀
  set K₁ : IntermediateField k (LaurentSeries k) := adjoin k ({jqModC k} : Set (LaurentSeries k)) with hK₁
  haveI : FiniteDimensional Lκ Fκ := hfd

  let ψ₀ : Lκ →+* LaurentSeries k :=
    (Φ φ).comp (((qExpFunctionFieldC κ Γ).val : Fκ →+* LaurentSeries κ).comp (algebraMap Lκ Fκ))
  have hψ₀ : ∀ a : Lκ, ψ₀ a = Φ φ ((a : Fκ) : LaurentSeries κ) := fun a => rfl
  have hLκmap : ∀ a : Lκ, ((a : Fκ) : LaurentSeries κ) ∈
      adjoin κ ({(x : LaurentSeries κ)} : Set (LaurentSeries κ)) :=
    fun a => coe_mem_adjoin_of_mem_adjoin (qExpFunctionFieldC κ Γ) x a.2
  have hψ₀mem : ∀ a : Lκ, ψ₀ a ∈ K₁ := by
    intro a
    rw [hψ₀]
    have h := map_mem_adjoin φ (hLκmap a)
    rwa [Set.image_singleton, hΦx] at h
  let ψ : Lκ →+* K₁ := ψ₀.codRestrict K₁ hψ₀mem
  have hψval : (algebraMap K₁ (LaurentSeries k)).comp ψ = ψ₀ := RingHom.ext fun a => rfl

  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Lκ) (M := Fκ)
  let T : Set (LaurentSeries k) := Set.range fun i : Fin n => Φ φ ((v i : Fκ) : LaurentSeries κ)
  haveI : Finite T := Set.finite_range _ |>.to_subtype

  have hTint : ∀ t ∈ T, IsIntegral K₁ t := by
    rintro t ⟨i, rfl⟩
    have hint : IsIntegral Lκ (v i) := Algebra.IsIntegral.isIntegral (v i)
    refine ⟨(minpoly Lκ (v i)).map ψ, (minpoly.monic hint).map ψ, ?_⟩
    have h0 : aeval (v i) (minpoly Lκ (v i)) = 0 := minpoly.aeval Lκ (v i)
    rw [aeval_def] at h0
    have h1 := congrArg (fun z : Fκ => Φ φ (z : LaurentSeries κ)) h0
    simp only [ZeroMemClass.coe_zero, map_zero] at h1
    have h2 : ((Φ φ).comp ((qExpFunctionFieldC κ Γ).val : Fκ →+* LaurentSeries κ))
        (eval₂ (algebraMap Lκ Fκ) (v i) (minpoly Lκ (v i))) = 0 := h1
    rw [hom_eval₂] at h2
    show eval₂ (algebraMap K₁ (LaurentSeries k)) (Φ φ ((v i : Fκ) : LaurentSeries κ))
      ((minpoly Lκ (v i)).map ψ) = 0
    rw [eval₂_map, hψval]
    exact h2

  have hsub : ∀ y : LaurentSeries κ, y ∈ Fκ → Φ φ y ∈ adjoin K₁ T := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Lκ).mp
      (show (⟨y, hy⟩ : Fκ) ∈ Submodule.span Lκ (Set.range v) by rw [hv]; trivial)
    have hy' : y = ∑ i, ((c i : Fκ) : LaurentSeries κ) * ((v i : Fκ) : LaurentSeries κ) := by
      have h := congrArg (fun z : Fκ => (z : LaurentSeries κ)) hc
      simp only at h
      rw [← h, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, MulMemClass.coe_mul]
    rw [hy', map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_mul]
    refine mul_mem ?_ (subset_adjoin K₁ T ⟨i, rfl⟩)
    have : Φ φ ((c i : Fκ) : LaurentSeries κ) = ((ψ (c i) : K₁) : LaurentSeries k) := rfl
    rw [this]
    exact IntermediateField.algebraMap_mem (adjoin K₁ T) (ψ (c i))

  haveI hfdT : FiniteDimensional K₁ (adjoin K₁ T) := finiteDimensional_adjoin hTint
  have hK₁F : K₁ ≤ Fk := by
    rw [hK₁, adjoin_le_iff, Set.singleton_subset_iff]
    exact hjk
  let N₁ : IntermediateField K₁ (LaurentSeries k) := extendScalars hK₁F
  have hN₁ : N₁ ≤ adjoin K₁ T := by
    intro z hz
    rw [mem_extendScalars] at hz
    have hz' : z ∈ (adjoin k ((Φ φ) '' intFormRatiosC κ Γ)) := by
      rw [image_intFormRatiosC]; exact hz

    have hle : adjoin k ((Φ φ) '' intFormRatiosC κ Γ) ≤ restrictScalars k (adjoin K₁ T) := by
      rw [adjoin_le_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact hsub y (intFormRatiosC_subset κ Γ hy)
    exact hle hz'
  haveI hfdN : FiniteDimensional K₁ N₁ :=
    Module.Finite.of_injective (IntermediateField.inclusion hN₁).toLinearMap
      (IntermediateField.inclusion_injective hN₁)

  have hmap : K₀.map (qExpFunctionFieldC k Γ).val = K₁ := by
    have h := adjoin_map k ({x'} : Set Fk) (qExpFunctionFieldC k Γ).val
    rw [Set.image_singleton] at h
    exact h
  let e₀ : K₀ ≃ₐ[k] K₁ := (K₀.equivMap (qExpFunctionFieldC k Γ).val).trans (equivOfEq hmap)
  have he₀ : ∀ b : K₀, ((e₀ b : K₁) : LaurentSeries k) = ((b : Fk) : LaurentSeries k) := by
    intro b
    rfl
  let e₂ : N₁ ≃+* Fk := RingEquiv.refl Fk
  refine Module.Finite.of_equiv_equiv (A₁ := K₁) (B₁ := N₁) (A₂ := K₀) (B₂ := Fk)
    e₀.symm.toRingEquiv e₂ ?_
  refine RingHom.ext fun a => ?_
  apply Subtype.ext
  change (((e₀.symm a : K₀) : Fk) : LaurentSeries k) = (a : LaurentSeries k)
  rw [← he₀ (e₀.symm a), AlgEquiv.apply_symm_apply]

end Transfer

section Residue

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem isAlgebraic_residueField :
    letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
      (Fact.out : p.Prime) hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := by
  letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
    (Fact.out : p.Prime) hA
  letI := ZMod.algebra (IsLocalRing.ResidueField A) p
  have hp : p.Prime := Fact.out
  refine ⟨fun ybar => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ybar

  have hyQ : IsAlgebraic ℚ (y : AlgebraicClosure ℚ) := by
    have h := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (y : AlgebraicClosure ℚ)
    convert h using 2 <;> first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  have hyalg : IsAlgebraic ℤ (y : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr hyQ
  obtain ⟨P, hP0, hPy⟩ := hyalg
  set Q := P.primPart with hQ
  have hc0 : P.content ≠ 0 := fun h => hP0 (content_eq_zero_iff.mp h)
  have hQy : aeval (y : AlgebraicClosure ℚ) Q = 0 := by
    have h1 : aeval (y : AlgebraicClosure ℚ) (C P.content * Q) = 0 := by
      rw [← eq_C_content_mul_primPart]; exact hPy
    rw [map_mul, aeval_C, mul_eq_zero] at h1
    exact h1.resolve_left ((map_ne_zero_iff _ (RingHom.injective_int _)).mpr hc0)

  have hQyA : eval₂ (Int.castRingHom A) y Q = 0 := by
    have hinj : Function.Injective A.subtype := Subtype.val_injective
    apply hinj
    rw [hom_eval₂, map_zero]
    have h2 : (A.subtype.comp (Int.castRingHom A)) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [h2]
    exact hQy

  set Qbar := Q.map (Int.castRingHom (ZMod p)) with hQbar
  have hQbar0 : Qbar ≠ 0 := by
    intro h0
    have hdvd : ∀ i, (p : ℤ) ∣ Q.coeff i := by
      intro i
      have hi := congrArg (fun R : (ZMod p)[X] => R.coeff i) h0
      simp only [hQbar, coeff_map, coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hi
    have hunit : IsUnit (p : ℤ) := (isPrimitive_primPart P) (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact hp.one_lt.ne' hunit
  refine ⟨Qbar, hQbar0, ?_⟩
  rw [aeval_def, hQbar, eval₂_map]
  have h3 : (algebraMap (ZMod p) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod p)) =
      (IsLocalRing.residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
  rw [h3, ← hom_eval₂, hQyA, map_zero]

end Residue

section CharZero

variable (K : Type*) [Field K]

theorem coe_eq_zero_of_mem_maximalIdeal_top {a : (⊤ : ValuationSubring K)}
    (ha : a ∈ IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) : (a : K) = 0 := by
  by_contra h
  apply (IsLocalRing.mem_maximalIdeal _).mp ha
  refine ⟨⟨a, ⟨(a : K)⁻¹, trivial⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h)
  · exact Subtype.ext (inv_mul_cancel₀ h)

def residueTopHom : IsLocalRing.ResidueField (⊤ : ValuationSubring K) →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) (⊤ : ValuationSubring K).subtype
    fun _ ha => coe_eq_zero_of_mem_maximalIdeal_top K ha

end CharZero

end QExpBaseChange

end

open QExpBaseChange in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC K Γ,
      (x : LaurentSeries K) = ModularCurve.jqModC K ∧ Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
    haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    letI := ZMod.algebra K p
    haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := isAlgebraic_residueField p A hA
    let φ : IsLocalRing.ResidueField A →+* K :=
      (IsAlgClosed.lift (R := ZMod p) (S := IsLocalRing.ResidueField A) (M := K)).toRingHom
    obtain ⟨x, hx, -, hfd, -⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        (AlgebraicClosure ℚ) A Γ hT
    exact transfer φ Γ x hx hfd
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨x, hx, -, hfd, -⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        K (⊤ : ValuationSubring K) Γ hT
    exact transfer (residueTopHom K) Γ x hx hfd

end S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (solution)
