-- Prove2me | solution 1 for HeckeCharacter.exists_admitsModulus_of_continuous_of_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dca23372-fbe0-5b59-ad85-f783e10a9b7b

import Mathlib
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain HeckeCharacter NumberField.AdelicLevel
open scoped nonZeroDivisors Topology

noncomputable section

namespace OpenKernelModulusSol

variable (K : Type*) [Field K] [NumberField K]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝔸Kf" => FiniteAdeleRing (𝓞 K) K

def finUnit : (𝔸Kf)ˣ →* (𝔸K)ˣ := Units.map (finIncl (𝓞 K) K)

theorem continuous_finIncl : Continuous (finIncl (𝓞 K) K) := by
  unfold finIncl
  exact Continuous.prodMk continuous_const continuous_id

theorem continuous_finUnit : Continuous (finUnit K) :=
  Continuous.units_map _ (continuous_finIncl K)

def sndUnit : (𝔸K)ˣ →* (𝔸Kf)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (𝔸Kf))

theorem finUnit_sndUnit {u : (𝔸K)ˣ} (hu : (u : 𝔸K).1 = 1) : finUnit K (sndUnit K u) = u := by
  refine Units.ext (Prod.ext ?_ rfl)
  show (1 : InfiniteAdeleRing K) = (u : 𝔸K).1
  exact hu.symm

theorem sndUnit_val (u : (𝔸K)ˣ) : ((sndUnit K u : (𝔸Kf)ˣ) : 𝔸Kf) = (u : 𝔸K).2 := rfl

variable {K}

theorem isOpen_ker {G : Type*} [Group G] [TopologicalSpace G] (χ : G →* ℂˣ)
    (hc : Continuous χ) (hfin : IsOfFinOrder χ) : IsOpen {g : G | χ g = 1} := by
  classical
  set n := orderOf χ with hn
  have hnpos : 0 < n := hfin.orderOf_pos
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hpow : ∀ g, χ g ^ n = 1 := fun g => by
    rw [← MonoidHom.pow_apply, hn, pow_orderOf_eq_one, MonoidHom.one_apply]

  set T : Set ℂˣ := {z | z ^ n = 1 ∧ z ≠ 1} with hT
  have hTfin : T.Finite := by
    have hfin' : {z : ℂˣ | z ^ n = 1}.Finite := by
      refine Set.Finite.of_finite_image ?_ Units.val_injective.injOn
      refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      simp only [Set.mem_setOf_eq] at hz
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hnpos, ← Units.val_pow_eq_pow_val,
        hz, Units.val_one]
    exact hfin'.subset fun z hz => hz.1
  have hTclosed : IsClosed T := hTfin.isClosed
  have hpre : {g : G | χ g = 1} = χ ⁻¹' Tᶜ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, hT, not_and, not_not]
    exact ⟨fun h _ => h, fun h => h (hpow g)⟩
  rw [hpre]
  exact hTclosed.isOpen_compl.preimage hc

open RestrictedProduct in

theorem exists_box_subset_of_mem_nhds_one {V : Set (𝔸Kf)} (hV : V ∈ 𝓝 (1 : 𝔸Kf)) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ x : 𝔸Kf, (∀ v, x v ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ I, Valued.v (x v - 1) ≤ WithZero.exp (-(n v : ℤ))) → x ∈ V := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    fun v => Valued.isOpen_valuationSubring _

  have h1 : (1 : 𝔸Kf) = structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
      (fun v => ⟨1, (v.adicCompletionIntegers K).one_mem⟩) := rfl
  have key := nhds_eq_map_structureMap hAopen
    (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))
  have hV' : V ∈ Filter.map (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite)
      (𝓝 (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))) := by
    rw [← key]
    exact hV
  have hV'' : (structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) ⁻¹' V ∈
      (𝓝 (fun v : HeightOneSpectrum (𝓞 K) => (⟨1, (v.adicCompletionIntegers K).one_mem⟩ :
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))))) := hV'
  rw [nhds_pi, Filter.mem_pi] at hV''
  obtain ⟨I, hI, t, ht, hIt⟩ := hV''

  have hball : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℕ, ∀ y : v.adicCompletionIntegers K,
      Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hu
    set δ : WithZero (Multiplicative ℤ) :=
      MonoidWithZeroHom.ValueGroup₀.embedding (γ.1 : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass
        (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))))) with hδ
    have hδ0 : δ ≠ 0 := by
      rw [hδ]
      exact (map_ne_zero _).mpr γ.ne_zero
    refine ⟨(WithZero.log δ).natAbs + 1, fun y hy => hut (hγ ?_)⟩
    show Valued.v.restrict ((y : v.adicCompletion K) - (1 : v.adicCompletionIntegers K)) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt hy ?_
    rw [← hδ]
    conv_rhs => rw [← WithZero.exp_log hδ0]
    rw [WithZero.exp_lt_exp]
    omega
  choose n hn using hball
  refine ⟨hI.toFinset, n, fun x hxint hxcong => ?_⟩

  have hx : x = structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite
      (fun v => ⟨x v, hxint v⟩) := RestrictedProduct.ext _ _ fun _ => rfl
  rw [hx]
  refine hIt (Set.mem_pi.mpr fun v hv => hn v _ ?_)
  exact hxcong v (hI.mem_toFinset.mpr hv)

def boxModulus (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    Ideal (𝓞 K) :=
  ∏ v ∈ I, v.asIdeal ^ n v

omit [NumberField K] in
theorem boxModulus_ne_bot (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    boxModulus I n ≠ ⊥ := by
  unfold boxModulus
  rw [Ne, ← Submodule.zero_eq_bot, Finset.prod_eq_zero_iff]
  rintro ⟨v, _, hv⟩
  exact v.ne_bot (by rw [← Submodule.zero_eq_bot]; exact eq_zero_of_pow_eq_zero hv)

theorem le_idealMultiplicity_boxModulus (I : Finset (HeightOneSpectrum (𝓞 K)))
    (n : HeightOneSpectrum (𝓞 K) → ℕ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ I) :
    n v ≤ idealMultiplicity K v (boxModulus I n) := by
  classical
  unfold idealMultiplicity
  have hdvd : v.asIdeal ^ n v ∣ boxModulus I n := Finset.dvd_prod_of_mem _ hv
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr (boxModulus_ne_bot I n))
    v.associates_irreducible, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
  exact hdvd

theorem valued_inv_sub_one {v : HeightOneSpectrum (𝓞 K)} {a : v.adicCompletion K}
    (ha : Valued.v a = 1) : Valued.v (a⁻¹ - 1) = Valued.v (a - 1) := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero] at ha; exact zero_ne_one ha
  have : a⁻¹ - 1 = a⁻¹ * (1 - a) := by field_simp
  rw [this, map_mul, map_inv₀, ha, inv_one, one_mul, Valuation.map_sub_swap]

theorem fad_units_inv_apply' (X : (𝔸Kf)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((X⁻¹ : (𝔸Kf)ˣ) : 𝔸Kf) v) = (((X : (𝔸Kf)ˣ) : 𝔸Kf) v)⁻¹ := by
  have h : ((X : 𝔸Kf) v) * (((X⁻¹ : (𝔸Kf)ˣ) : 𝔸Kf) v) = 1 :=
    congrArg (fun a : 𝔸Kf => a v) X.mul_inv
  exact (eq_inv_of_mul_eq_one_right h)

end OpenKernelModulusSol

end

open OpenKernelModulusSol NumberField AutomorphicForm IsDedekindDomain HeckeCharacter NumberField.AdelicLevel Topology in

theorem solution
    (K : Type*) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hc : Continuous χ) (hfin : IsOfFinOrder χ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧ AdmitsModulus K χ 𝔣 := by
  classical

  have hopen : IsOpen {y : (FiniteAdeleRing (𝓞 K) K)ˣ | χ (finUnit K y) = 1} :=
    (isOpen_ker χ hc hfin).preimage (continuous_finUnit K)
  have h1mem : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ {y : (FiniteAdeleRing (𝓞 K) K)ˣ | χ (finUnit K y) = 1} := by
    simp

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp hopen
  have h1t : ((1 : FiniteAdeleRing (𝓞 K) K), (1 : (FiniteAdeleRing (𝓞 K) K)ᵐᵒᵖ)) ∈ t := by
    have h := h1mem
    rw [← hteq, Set.mem_preimage, map_one] at h
    exact h
  obtain ⟨U₁, U₂, hU₁, hU₂, h1U₁, h1U₂, hprod⟩ := isOpen_prod_iff.mp ht 1 1 h1t
  set V : Set (FiniteAdeleRing (𝓞 K) K) := U₁ ∩ MulOpposite.op ⁻¹' U₂ with hVdef
  have hV : V ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K) :=
    (hU₁.inter (hU₂.preimage MulOpposite.continuous_op)).mem_nhds ⟨h1U₁, h1U₂⟩
  obtain ⟨I, n, hbox⟩ := exists_box_subset_of_mem_nhds_one hV
  refine ⟨boxModulus I n, boxModulus_ne_bot I n, ?_⟩
  intro u hu1 hu2
  set y : (FiniteAdeleRing (𝓞 K) K)ˣ := sndUnit K u with hydef
  have hy : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
      Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
        WithZero.exp (-(idealMultiplicity K v (boxModulus I n) : ℤ)) := hu2
  have hcong : ∀ v ∈ I,
      Valued.v (((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤
        WithZero.exp (-(n v : ℤ)) := fun v hv =>
    (hy v).2.trans (WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr
      (le_idealMultiplicity_boxModulus I n hv))))
  have hyV : ((y : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈ V :=
    hbox _ (fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hy v).1.le) hcong
  have hyinvV : (((y⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ)) : FiniteAdeleRing (𝓞 K) K) ∈ V := by
    refine hbox _ (fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_) (fun v hv => ?_)
    · rw [fad_units_inv_apply', map_inv₀, (hy v).1, inv_one]
    · rw [fad_units_inv_apply', valued_inv_sub_one (hy v).1]
      exact hcong v hv
  have hyker : χ (finUnit K y) = 1 := by
    have hemb : Units.embedProduct _ y ∈ t := hprod ⟨hyV.1, hyinvV.2⟩
    have h : y ∈ Units.embedProduct _ ⁻¹' t := hemb
    rw [hteq] at h
    exact h
  rw [← finUnit_sndUnit K hu1]
  exact hyker

end S_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder
end P2MW
export P2MW.S_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder (solution)
