-- Prove2me | solution 1 for HeckeCharacter.IsFiniteOrderHeckeChar.exists_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/45b3110a-7eeb-5fbf-b2d4-dd8a0c38c1e3

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel RatIdele
open scoped Topology

namespace P124

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem isOpen_ker_of_continuous_of_isOfFinOrder {G : Type*} [Group G] [TopologicalSpace G]
    {f : G →* ℂˣ} (hf : Continuous f) (hfin : IsOfFinOrder f) : IsOpen (f.ker : Set G) := by
  classical
  obtain ⟨m, hm, hfm⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hroot : ∀ u : G, ((f u : ℂ)) ^ m = 1 := fun u => by
    have h2 : (f u) ^ m = 1 := by rw [← MonoidHom.pow_apply, hfm, MonoidHom.one_apply]
    have h3 := congrArg Units.val h2
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h3
  set S : Set ℂ := {z : ℂ | z ^ m = 1 ∧ z ≠ 1} with hS_def
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Polynomial.nthRootsFinset m (1 : ℂ)).finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hm]
    exact hz.1
  have hker : (f.ker : Set G) = (fun u : G => ((f u : ℂ))) ⁻¹' Sᶜ := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, hS_def,
      Set.mem_setOf_eq, not_and, not_not]
    constructor
    · intro h _
      rw [h, Units.val_one]
    · intro h
      exact Units.ext (h (hroot u))
  rw [hker]
  exact hSfin.isClosed.isOpen_compl.preimage (Units.continuous_val.comp hf)

theorem continuous_finIncl : Continuous (finIncl (𝓞 ℚ) ℚ : 𝔸ℚf → 𝔸ℚ) := by
  show Continuous fun y : 𝔸ℚf => ((1, y) : InfiniteAdeleRing ℚ × 𝔸ℚf)
  exact continuous_const.prodMk continuous_id

theorem finIncl_snd_of_fst_eq_one {a : 𝔸ℚ} (ha : a.1 = 1) : finIncl (𝓞 ℚ) ℚ a.2 = a :=
  Prod.ext ha.symm rfl

theorem valued_natCast_le_of_dvd (v : HeightOneSpectrum (𝓞 ℚ)) {d N : ℕ} (h : d ∣ N) :
    Valued.v (((N : ℕ) : v.adicCompletion ℚ)) ≤ Valued.v (((d : ℕ) : v.adicCompletion ℚ)) := by
  obtain ⟨e, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  refine mul_le_of_le_one_right' ?_
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((e : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((e : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) e).symm,
    valuation_of_algebraMap]
  exact intValuation_le_one v _

theorem valued_natGenerator_pow (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    Valued.v ((((natGenerator v) ^ k : ℕ) : v.adicCompletion ℚ)) = exp (-(k : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat, Nat.cast_pow, map_pow,
    valuation_natGenerator, ← exp_nsmul]
  simp

theorem exists_level_of_mem_nhds_one {U : Set (𝔸ℚ)ˣ} (hU : U ∈ 𝓝 (1 : (𝔸ℚ)ˣ)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ u : (𝔸ℚ)ˣ, (u : 𝔸ℚ).1 = 1 →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : 𝔸ℚ).2 v) = 1 ∧
        Valued.v ((u : 𝔸ℚ).2 v - 1) ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ))) → u ∈ U := by
  classical

  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [Units.embedProduct_apply, inv_one, Units.val_one, MulOpposite.op_one, nhds_prod_eq,
    Filter.mem_prod_iff] at hV
  obtain ⟨A, hA, B, hB, hAB⟩ := hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : 𝔸ℚ) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rwa [MulOpposite.op_one])

  set C : Set 𝔸ℚf := (finIncl (𝓞 ℚ) ℚ) ⁻¹' A ∩ (finIncl (𝓞 ℚ) ℚ) ⁻¹' (MulOpposite.op ⁻¹' B) with hC
  have hC1 : C ∈ 𝓝 (1 : 𝔸ℚf) := by
    refine Filter.inter_mem ?_ ?_
    · exact continuous_finIncl.continuousAt.preimage_mem_nhds (by rwa [map_one])
    · exact continuous_finIncl.continuousAt.preimage_mem_nhds (by rwa [map_one])

  set σ := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite with hσ
  have hσ1 : σ 1 = 1 := rfl
  have hT : σ ⁻¹' C ∈ 𝓝 (1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) :=
    (RestrictedProduct.isEmbedding_structureMap.continuous.continuousAt (x := 1)).preimage_mem_nhds
      (hC1 : C ∈ 𝓝 (σ 1))
  rw [nhds_pi, Filter.mem_pi] at hT
  obtain ⟨I, hIfin, t, ht, htsub⟩ := hT

  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ k : ℕ, ∀ y : v.adicCompletionIntegers ℚ,
      Valued.v ((y : v.adicCompletion ℚ) - 1) ≤ exp (-(k : ℤ)) → y ∈ t v := by
    intro v
    have htv := ht v
    rw [nhds_subtype, Filter.mem_comap] at htv
    obtain ⟨s, hs, hst⟩ := htv
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs

    set g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding
      (γ : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰))) with hgdef
    have hg0 : g ≠ 0 := (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℕ, exp (-(k : ℤ)) < g := by
      refine ⟨(-log g).toNat + 1, ?_⟩
      conv_rhs => rw [← exp_log hg0]
      rw [exp_lt_exp]
      omega
    refine ⟨k, fun y hy => hst ?_⟩
    rw [Set.mem_preimage]
    apply hγ
    show Valued.v.restrict ((y : v.adicCompletion ℚ) - ((1 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ))
      < ((γ : (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰)))ˣ) :
          MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰)))
    rw [OneMemClass.coe_one, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hy hk
  choose k hk using hloc

  set N : ℕ := ∏ v ∈ hIfin.toFinset, (natGenerator v) ^ (k v) with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (prime_natGenerator v).ne_zero
  refine ⟨N, hN0, fun u hu1 huv => ?_⟩

  have hmemC : ∀ w : (𝔸ℚ)ˣ, (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((w : 𝔸ℚ).2 v) = 1 ∧
      Valued.v ((w : 𝔸ℚ).2 v - 1) ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ))) → (w : 𝔸ℚ).2 ∈ C := by
    intro w hw
    set y : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ :=
      fun v => ⟨(w : 𝔸ℚ).2 v, (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hw v).1.le⟩ with hy
    have hyw : σ y = (w : 𝔸ℚ).2 := RestrictedProduct.ext _ _ fun v => rfl
    rw [← hyw]
    show y ∈ σ ⁻¹' C
    refine htsub fun v hv => hk v (y v) ?_
    have hvI : v ∈ hIfin.toFinset := hIfin.mem_toFinset.mpr hv
    calc Valued.v (((y v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) - 1)
        = Valued.v ((w : 𝔸ℚ).2 v - 1) := rfl
      _ ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ)) := (hw v).2
      _ ≤ Valued.v ((((natGenerator v) ^ (k v) : ℕ) : v.adicCompletion ℚ)) :=
          valued_natCast_le_of_dvd v (Finset.dvd_prod_of_mem (fun w => (natGenerator w) ^ (k w)) hvI)
      _ = exp (-(k v : ℤ)) := valued_natGenerator_pow v (k v)
  have hinv1 : (((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).1 = 1 := by
    have h := congrArg Prod.fst u.inv_val
    rw [show ((u.inv * u.val : 𝔸ℚ)).1 = ((u⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).1 * (u : 𝔸ℚ).1 from rfl, hu1, mul_one] at h
    exact h
  have huinv : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) = 1 ∧
      Valued.v ((((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v - 1) ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ)) := by
    intro v
    have hmul : (((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v * (u : 𝔸ℚ).2 v = 1 := by
      rw [← valued_snd_inv_mul u v] at *
      have h := congrArg (fun a : 𝔸ℚ => a.2 v) u.inv_val
      exact h
    have h1 : Valued.v ((((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) = 1 := by
      have h := valued_snd_inv_mul u v
      rwa [(huv v).1, mul_one] at h
    refine ⟨h1, ?_⟩
    have hrw : (((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v - 1 = -((((u⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v * ((u : 𝔸ℚ).2 v - 1)) := by
      rw [mul_sub, hmul, mul_one, neg_sub]
    rw [hrw, Valuation.map_neg, map_mul, h1, one_mul]
    exact (huv v).2
  apply hVU
  rw [Set.mem_preimage, Units.embedProduct_apply]
  apply hAB
  refine Set.mk_mem_prod ?_ ?_
  · rw [← finIncl_snd_of_fst_eq_one hu1]
    exact (hmemC u huv).1
  · show MulOpposite.op ((u⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ) ∈ B
    rw [← finIncl_snd_of_fst_eq_one hinv1]
    exact (hmemC u⁻¹ huinv).2

end P124

namespace P124

open RatIdele

theorem valued_natCast_eq_exp_neg_idealMultiplicity' (N : ℕ) [NeZero N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((N : ℕ) : v.adicCompletion ℚ))
      = exp (-(HeckeCharacter.idealMultiplicity ℚ v (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((N : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((N : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) N).symm,
    valuation_of_algebraMap, intValuation_if_neg v (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  rfl

theorem exists_admitsModulus_port {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ N : ℕ, N ≠ 0 ∧ HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := by
  have hker : (μ.ker : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    (isOpen_ker_of_continuous_of_isOfFinOrder hμ.continuous hμ.isOfFinOrder).mem_nhds (μ.mem_ker.mpr (map_one μ))
  obtain ⟨N, hN0, hN⟩ := exists_level_of_mem_nhds_one hker
  haveI : NeZero N := ⟨hN0⟩
  refine ⟨N, hN0, fun u hu1 huv => μ.mem_ker.mp (hN u hu1 fun v => ⟨(huv v).1, ?_⟩)⟩
  rw [valued_natCast_eq_exp_neg_idealMultiplicity']
  exact (huv v).2

end P124

end

open NumberField IsDedekindDomain

theorem solution
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ N : ℕ, N ≠ 0 ∧ HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) :=
  P124.exists_admitsModulus_port hμ

end S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus
end P2MW
export P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus (solution)
