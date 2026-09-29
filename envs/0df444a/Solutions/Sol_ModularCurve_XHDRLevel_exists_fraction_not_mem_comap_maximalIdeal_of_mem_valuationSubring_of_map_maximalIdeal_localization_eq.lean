-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/20b22b41-1f18-5a35-a7c2-fc16675f6c6e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
import Theorems.Thm_Localization_AtPrime_mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace BranchReadSkel

open ModularCurve AlgebraicCurve

def toSubringHom {T F : Type*} [CommRing T] [Field F] (γ : T →+* F) (V : ValuationSubring F) (h : ∀ t, γ t ∈ V) : T →+* ↥V where
  toFun t := ⟨γ t, h t⟩
  map_one' := Subtype.ext (map_one γ)
  map_mul' a b := Subtype.ext (map_mul γ a b)
  map_zero' := Subtype.ext (map_zero γ)
  map_add' a b := Subtype.ext (map_add γ a b)

@[scoped simp] theorem toSubringHom_apply {T F : Type*} [CommRing T] [Field F] (γ : T →+* F) (V : ValuationSubring F) (h : ∀ t, γ t ∈ V) (t : T) :
    toSubringHom γ V h t = ⟨γ t, h t⟩ := rfl

section S3
variable {F T : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {A : ValuationSubring (AlgebraicClosure ℚ)} [CommRing T]

theorem comap_branch_eq_maximalIdeal (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (ι : ↥A →+* T) (hγA : ∀ a : ↥A, γ (ι a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    𝔯.comap ι = IsLocalRing.maximalIdeal ↥A := by
  ext a
  rw [Ideal.mem_comap, h𝔯def, ← hW𝔪 a]
  have hmem : (⟨γ (ι a), hγW (ι a)⟩ : ↥W) = ⟨algebraMap (AlgebraicClosure ℚ) F a, hWA a⟩ := Subtype.ext (hγA a)
  rw [hmem]

theorem map_maximalIdeal_le_branch (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (ι : ↥A →+* T) (hγA : ∀ a : ↥A, γ (ι a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W) :
    (IsLocalRing.maximalIdeal ↥A).map ι ≤ 𝔯 := by
  rw [Ideal.map_le_iff_le_comap, comap_branch_eq_maximalIdeal W γ hγW ι hγA hWA hW𝔪 𝔯 h𝔯def]

theorem mem_of_fraction (W : ValuationSubring F) (γ : T →+* F) (hγW : ∀ t, γ t ∈ W)
    (𝔯 : Ideal T) (h𝔯def : ∀ t, t ∈ 𝔯 ↔ (⟨γ t, hγW t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    (h : F) (a c : T) (hc : c ∉ 𝔯) (hfac : h * γ c = γ a) : h ∈ W := by
  rw [h𝔯def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
  have hc0 : γ c ≠ 0 := by
    intro h0
    apply hc.ne_zero
    exact Subtype.ext h0
  have hh : h = γ a * (γ c)⁻¹ := by rw [← hfac, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  have hinv : ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).1 = (γ c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have hu := congrArg Subtype.val hc.unit.mul_inv
    rw [IsUnit.unit_spec] at hu
    exact hu
  rw [hh, ← hinv]
  exact mul_mem (hγW a) ((hc.unit⁻¹ : (↥W)ˣ) : ↥W).2

end S3

theorem exists_pow_mem_span_natCast_of_mem_maximalIdeal (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    ∃ k : ℕ, m ^ k ∈ Ideal.span {((p : ℕ) : ↥A)} := by
  classical

  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(m : AlgebraicClosure ℚ)} with hL
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (m : AlgebraicClosure ℚ)).isIntegral)
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥L (AlgebraicClosure ℚ))) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hp.out hA
  set AL := A.comap (algebraMap ↥L (AlgebraicClosure ℚ)) with hAL

  have hmL : (m : AlgebraicClosure ℚ) ∈ L := IntermediateField.mem_adjoin_simple_self ℚ _
  set mL : ↥AL := ⟨⟨(m : AlgebraicClosure ℚ), hmL⟩, by show algebraMap ↥L (AlgebraicClosure ℚ) ⟨m, hmL⟩ ∈ A; exact m.2⟩ with hmLdef
  set pL : ↥AL := ⟨((p : ℕ) : ↥L), by show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) ∈ A; rw [map_natCast]; exact natCast_mem A p⟩ with hpLdef

  let ι : ↥AL →+* ↥A :=
    { toFun := fun x => ⟨algebraMap ↥L (AlgebraicClosure ℚ) x.1, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hιm : ι mL = m := Subtype.ext rfl
  have hιp : ι pL = ((p : ℕ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) = ((p : ↥A) : AlgebraicClosure ℚ)
    rw [map_natCast]; rfl

  have hp0 : pL ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥AL => ((x.1 : ↥L) : AlgebraicClosure ℚ)) h
    simp only [hpLdef] at this
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0) (by simpa using this)
  have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    have hc : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
    rw [← hc]
    exact hmem
  have key : ∀ x : ↥AL, ι x ∈ maximalIdeal ↥A → x ∈ maximalIdeal ↥AL := fun x hx => by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map ι)
  have hpnu : pL ∈ maximalIdeal ↥AL := key pL (by rw [hιp]; exact hpA)
  have hmnu : mL ∈ maximalIdeal ↥AL := key mL (by rw [hιm]; exact hm)

  have hrad : mL ∈ (Ideal.span {pL}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJne : J ≠ ⊥ := fun h => hp0 (by
      have : pL ∈ J := hJ (Ideal.subset_span rfl)
      rw [h] at this
      exact (Submodule.mem_bot _).mp this)
    have hJmax : J = maximalIdeal ↥AL := IsLocalRing.eq_maximalIdeal (hJp.isMaximal hJne)
    rw [hJmax]; exact hmnu
  obtain ⟨k, hk⟩ := hrad
  refine ⟨k, ?_⟩
  have := Ideal.mem_map_of_mem ι hk
  rw [Ideal.map_span, Set.image_singleton, hιp, map_pow, hιm] at this
  exact this

theorem isFractionRing_of_injective_of_forall_exists
    {T : Type*} [CommRing T] [IsDomain T] (𝔔 : Ideal T) [𝔔.IsPrime]
    {F : Type*} [Field F] (γ : T →+* F) (hγ : Function.Injective γ)
    (hfrac : ∀ e : F, ∃ a s : T, s ≠ 0 ∧ e * γ s = γ a)
    [Algebra (Localization.AtPrime 𝔔) F]
    (halg : ∀ t : T, algebraMap (Localization.AtPrime 𝔔) F (algebraMap T _ t) = γ t) :
    IsFractionRing (Localization.AtPrime 𝔔) F := by
  classical
  have hle : 𝔔.primeCompl ≤ nonZeroDivisors T := by
    intro s hs
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hs (h0 ▸ 𝔔.zero_mem))
  haveI : IsDomain (Localization.AtPrime 𝔔) := IsLocalization.isDomain_localization hle
  have hmk : ∀ (a : T) (s : 𝔔.primeCompl),
      algebraMap (Localization.AtPrime 𝔔) F (IsLocalization.mk' _ a s) * γ s = γ a := by
    intro a s
    rw [← halg s, ← map_mul, IsLocalization.mk'_spec, halg]
  have hinjS : Function.Injective (algebraMap (Localization.AtPrime 𝔔) F) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl x
    have h1 := hmk a s
    simp only at hx
    rw [hx, zero_mul] at h1
    have ha : a = 0 := hγ (by rw [← h1, map_zero])
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    apply IsUnit.mk0
    rw [map_ne_zero_iff _ hinjS]
    exact nonZeroDivisors.ne_zero y.2
  · intro e
    obtain ⟨a, s, hs, he⟩ := hfrac e
    refine ⟨⟨algebraMap T _ a, ⟨algebraMap T _ s, ?_⟩⟩, ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero
        (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ hle (mem_nonZeroDivisors_of_ne_zero hs))
    · simp only [halg]
      exact he
  · intro x y hxy
    exact ⟨1, by simpa using hinjS hxy⟩

set_option maxHeartbeats 3200000 in
theorem fraction_of_mem
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Algebra.FiniteType (R p) B] [Module.Flat (R p) B]
    (W : ValuationSubring ↥(xHFunctionFieldBar M H))
    (γ : (↥A ⊗[R p] B) →+* ↥(xHFunctionFieldBar M H)) (hγG : ∀ t, γ t ∈ W)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] B), s ≠ 0 ∧ e * γ s = γ a)
    (hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (hpW : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ W.nonunits)
    (𝔯₀ : Ideal (↥A ⊗[R p] B)) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    [h𝔯₀ : 𝔯₀.IsPrime]
    (hmin : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀))
    (h : ↥(xHFunctionFieldBar M H)) (hh : h ∈ W) :
    ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ h * γ c = γ a := by
  classical

  haveI hTdom : IsDomain (↥A ⊗[R p] B) := hγinj.isDomain γ
  haveI hSdom : IsDomain (Localization.AtPrime 𝔯₀) := IsLocalization.isDomain_localization 𝔯₀.primeCompl_le_nonZeroDivisors
  have hγne : ∀ c : 𝔯₀.primeCompl, IsUnit (γ c) := fun c =>
    ((map_ne_zero_iff _ hγinj).mpr (fun h0 => c.2 (by rw [h0]; exact 𝔯₀.zero_mem))).isUnit
  letI algSF : Algebra (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H) := (IsLocalization.lift (M := 𝔯₀.primeCompl) hγne).toAlgebra
  have halgSF : ∀ c : (↥A ⊗[R p] B),
      algebraMap (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H) (algebraMap _ (Localization.AtPrime 𝔯₀) c) = γ c :=
    fun c => IsLocalization.lift_eq (M := 𝔯₀.primeCompl) hγne c
  haveI hfracSF : IsFractionRing (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H) :=
    isFractionRing_of_injective_of_forall_exists 𝔯₀ γ hγinj hγfrac halgSF
  have hinjSF : Function.Injective (algebraMap (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H)) :=
    IsFractionRing.injective (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H)
  have hincl : (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom := RingHom.ext fun _ => rfl

  have h𝔯₀A : 𝔯₀.comap (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom =
      IsLocalRing.maximalIdeal ↥A := by
    rw [hincl]; exact comap_branch_eq_maximalIdeal W γ hγG _ hγA hWA hW𝔪 𝔯₀ h𝔯₀def
  have h𝔭 : ((IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
      (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom)).IsPrime := by
    rw [hmin]; infer_instance
  obtain ⟨-, hval⟩ :=
    Localization.AtPrime.mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
      p A hA ρ hρ halg B 𝔯₀ h𝔯₀A h𝔭 ↥(xHFunctionFieldBar M H)

  have hrange_iff : ∀ e : ↥(xHFunctionFieldBar M H), e ∈ RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) ↔
      ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ e * γ c = γ a := by
    intro e
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨a, c, rfl⟩ := IsLocalization.exists_mk'_eq 𝔯₀.primeCompl z
      exact ⟨a, c, c.2, by rw [← halgSF, ← halgSF, ← map_mul, IsLocalization.mk'_spec]⟩
    · rintro ⟨a, c, hc, hfac⟩
      refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔯₀) a (⟨c, hc⟩ : 𝔯₀.primeCompl), ?_⟩
      have hc0 : γ c ≠ 0 := (hγne ⟨c, hc⟩).ne_zero
      apply mul_right_cancel₀ hc0
      rw [hfac, ← halgSF c, ← map_mul, ← halgSF a]
      congr 1
      exact IsLocalization.mk'_spec (Localization.AtPrime 𝔯₀) a (⟨c, hc⟩ : 𝔯₀.primeCompl)
  have hval' : ∀ e : ↥(xHFunctionFieldBar M H), e ∈ RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) ∨
      e⁻¹ ∈ RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) := by
    intro e

    have tr : ∀ f : ↥(xHFunctionFieldBar M H), (∃ a c : Localization.AtPrime 𝔯₀, c ∉ (IsLocalRing.maximalIdeal ↥A).map
        ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) ∧
        f * algebraMap _ ↥(xHFunctionFieldBar M H) c = algebraMap _ ↥(xHFunctionFieldBar M H) a) → f ∈ RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) := by
      rintro f ⟨a, c, hc, hfac⟩
      rw [hmin, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
      refine ⟨a * ↑(hc.unit⁻¹), ?_⟩
      rw [map_mul, ← hfac, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
    rcases hval e with h1 | h2
    · exact Or.inl (tr e h1)
    · exact Or.inr (tr e⁻¹ h2)
  let V₀ : ValuationSubring ↥(xHFunctionFieldBar M H) :=
    { RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) with
      mem_or_inv_mem' := hval' }
  have hV₀mem : ∀ e : ↥(xHFunctionFieldBar M H), e ∈ V₀ ↔ e ∈ RingHom.range (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _) := fun e => Iff.rfl

  have hVW : V₀ ≤ W := by
    intro e he
    obtain ⟨a, c, hc, hfac⟩ := (hrange_iff e).mp ((hV₀mem e).mp he)
    exact mem_of_fraction W γ hγG 𝔯₀ h𝔯₀def e a c hc hfac

  have hpV : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ V₀ := by
    rw [hV₀mem, hrange_iff]
    refine ⟨Algebra.TensorProduct.includeLeftRingHom ((p : ℕ) : ↥A), 1, fun h1 => h𝔯₀.ne_top ((Ideal.eq_top_iff_one _).mpr h1), ?_⟩
    rw [map_one, mul_one, hγA]; simp

  have hrad : IsLocalRing.maximalIdeal ↥V₀ ≤ (Ideal.span {(⟨_, hpV⟩ : ↥V₀)}).radical := by
    intro e he
    let φ : Localization.AtPrime 𝔯₀ →+* ↥V₀ :=
      RingHom.rangeRestrict (R := Localization.AtPrime 𝔯₀) (S := ↥(xHFunctionFieldBar M H)) (algebraMap _ _)
    have hφ : Function.Surjective φ := RingHom.rangeRestrict_surjective _
    have hφval : ∀ z, ((φ z : ↥V₀) : ↥(xHFunctionFieldBar M H)) = algebraMap (Localization.AtPrime 𝔯₀) ↥(xHFunctionFieldBar M H) z := fun z => rfl
    obtain ⟨z, rfl⟩ := hφ e
    have hz : z ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at he ⊢
      exact fun hu => he (hu.map φ)
    rw [← hmin] at hz
    have hle : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) ≤
        (Ideal.span {((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
          (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) ((p : ℕ) : ↥A)}).radical := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      obtain ⟨k, hk⟩ := exists_pow_mem_span_natCast_of_mem_maximalIdeal p A hA m hm
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have := Ideal.mem_map_of_mem ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) hk
      rwa [Ideal.map_span, Set.image_singleton] at this
    obtain ⟨k, hk⟩ := hle hz
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have hmem := Ideal.mem_map_of_mem φ hk
    rw [Ideal.map_span, Set.image_singleton] at hmem
    have hpe : φ (((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
          (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) ((p : ℕ) : ↥A)) =
        (⟨_, hpV⟩ : ↥V₀) := by
      apply Subtype.ext
      rw [hφval, RingHom.comp_apply, halgSF, hincl, hγA]
      simp
    rw [hpe] at hmem
    exact hmem

  have hVeq : V₀ = W :=
    ValuationSubring.eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical V₀ W hVW ⟨_, hpV⟩ hpW hrad
  have hhV : h ∈ V₀ := by rw [hVeq]; exact hh
  exact (hrange_iff h).mp ((hV₀mem h).mp hhV)

end BranchReadSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq.BranchReadSkel"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Algebra.FiniteType (R p) B] [Module.Flat (R p) B]
    (W : ValuationSubring ↥(xHFunctionFieldBar M H))
    (γ : (↥A ⊗[R p] B) →+* ↥(xHFunctionFieldBar M H)) (hγG : ∀ t, γ t ∈ W)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] B), s ≠ 0 ∧ e * γ s = γ a)
    (hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (hpW : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ W.nonunits)
    (𝔯₀ : Ideal (↥A ⊗[R p] B)) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    [h𝔯₀ : 𝔯₀.IsPrime]
    (hmin : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀))
    (h : ↥(xHFunctionFieldBar M H)) (hh : h ∈ W) :
    ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ h * γ c = γ a :=
  BranchReadSkel.fraction_of_mem p M H hpM A hA ρ hρ halg B W γ hγG hγinj hγfrac hγA hWA hW𝔪 hpW 𝔯₀ h𝔯₀def hmin h hh

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq.BranchReadSkel"

end S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq (solution)
