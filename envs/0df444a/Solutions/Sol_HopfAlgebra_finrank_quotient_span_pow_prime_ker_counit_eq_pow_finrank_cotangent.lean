-- Prove2me | solution 1 for HopfAlgebra.finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2781e387-49b4-5d0c-908e-22619cddec36

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit
import Theorems.Thm_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe v

open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent"
namespace KerFrobC12
p2m_open "HopfAlgebra"

section TruncCount

open MvPolynomial

variable (k : Type*) [Field k] (d m : ℕ)

private noncomputable def truncIdeal : Ideal (MvPolynomial (Fin d) k) :=
  Ideal.span (Set.range fun i : Fin d => (X i : MvPolynomial (Fin d) k) ^ m)

private def bigSet : Set (Fin d →₀ ℕ) := {α | ∃ i, m ≤ α i}

private def smallSet : Set (Fin d →₀ ℕ) := {α | ∀ i, α i < m}

private theorem compl_bigSet : (bigSet d m)ᶜ = smallSet d m := by
  ext α
  simp [bigSet, smallSet]

private theorem mem_truncIdeal_iff (f : MvPolynomial (Fin d) k) :
    f ∈ truncIdeal k d m ↔ ∀ α ∈ f.support, ∃ i, m ≤ α i := by
  have h : truncIdeal k d m = Ideal.span ((fun s => monomial s (1 : k)) ''
      Set.range fun i : Fin d => Finsupp.single i m) := by
    rw [truncIdeal, ← Set.range_comp]
    congr 1
    ext i : 1
    simp [X_pow_eq_monomial]
  rw [h, mem_ideal_span_monomial_image]
  refine forall₂_congr fun α _ => ?_
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hi⟩
    exact ⟨i, Finsupp.single_le_iff.mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, ⟨i, rfl⟩, Finsupp.single_le_iff.mpr hi⟩

private theorem restrictScalars_truncIdeal :
    (truncIdeal k d m).restrictScalars k = restrictSupport k (bigSet d m) := by
  ext f
  rw [Submodule.restrictScalars_mem, mem_truncIdeal_iff, mem_restrictSupport_iff]
  rfl

private theorem isCompl_restrictSupport :
    IsCompl ((truncIdeal k d m).restrictScalars k) (restrictSupport k (smallSet d m)) := by
  rw [restrictScalars_truncIdeal, ← compl_bigSet]
  refine IsCompl.of_eq ?_ ?_
  · refine eq_bot_iff.2 fun x hx => ?_
    have hx' : AddMonoidAlgebra.coeff x ∈
        Finsupp.supported k k (bigSet d m) ⊓ Finsupp.supported k k (bigSet d m)ᶜ := ⟨hx.1, hx.2⟩
    rw [(Finsupp.disjoint_supported_supported disjoint_compl_right).eq_bot, Submodule.mem_bot] at hx'
    exact (Submodule.mem_bot k).2 (AddMonoidAlgebra.coeff_injective (by simpa using hx'))
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : AddMonoidAlgebra.coeff x ∈
        Finsupp.supported k k (bigSet d m) ⊔ Finsupp.supported k k (bigSet d m)ᶜ := by
      rw [← Finsupp.supported_union, Set.union_compl_self, Finsupp.supported_univ]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
    have hxab : x = AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b :=
      AddMonoidAlgebra.coeff_injective (by simp [hab])
    rw [hxab]
    exact Submodule.add_mem_sup
      (AddMonoidAlgebra.mem_supported.2 ((Finsupp.mem_supported k a).1 ha))
      (AddMonoidAlgebra.mem_supported.2 ((Finsupp.mem_supported k b).1 hb))

private noncomputable def smallSetEquiv : smallSet d m ≃ (Fin d → Fin m) where
  toFun α := fun i => ⟨α.1 i, α.2 i⟩
  invFun g := ⟨Finsupp.equivFunOnFinite.symm fun i => (g i : ℕ), fun i => by simp⟩
  left_inv α := by
    ext i
    simp
  right_inv g := by
    funext i
    ext
    simp

private noncomputable def quotTruncEquiv :
    (MvPolynomial (Fin d) k ⧸ truncIdeal k d m) ≃ₗ[k] restrictSupport k (smallSet d m) :=
  (Submodule.Quotient.restrictScalarsEquiv k (truncIdeal k d m)).symm.trans
    (Submodule.quotientEquivOfIsCompl _ _ (isCompl_restrictSupport k d m))

private theorem finite_and_finrank_quotient_truncIdeal :
    Module.Finite k (MvPolynomial (Fin d) k ⧸ truncIdeal k d m) ∧
    Module.finrank k (MvPolynomial (Fin d) k ⧸ truncIdeal k d m) = m ^ d := by
  classical
  let b : Module.Basis (smallSet d m) k (restrictSupport k (smallSet d m)) :=
    basisRestrictSupport k (smallSet d m)
  haveI : Finite (smallSet d m) := Finite.of_equiv _ (smallSetEquiv d m).symm
  haveI : Module.Finite k (restrictSupport k (smallSet d m)) := Module.Finite.of_basis b
  refine ⟨Module.Finite.equiv (quotTruncEquiv k d m).symm, ?_⟩
  rw [(quotTruncEquiv k d m).finrank_eq, Module.finrank_eq_nat_card_basis b,
    Nat.card_congr (smallSetEquiv d m), Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

end TruncCount

section Poly

open MvPolynomial
open scoped Pointwise

variable (k : Type*) [Field k] (d : ℕ)

private noncomputable def mX : Ideal (MvPolynomial (Fin d) k) := Ideal.span (Set.range X)

private theorem mem_mX_iff (f : MvPolynomial (Fin d) k) : f ∈ mX k d ↔ ∀ s ∈ f.support, s ≠ 0 := by
  rw [mX, ← Set.image_univ, mem_ideal_span_X_image]
  refine forall₂_congr fun s _ => ?_
  simp [Finsupp.ne_iff]

private theorem ker_constantCoeff :
    RingHom.ker (constantCoeff : MvPolynomial (Fin d) k →+* k) = mX k d := by
  ext f
  rw [RingHom.mem_ker, mem_mX_iff, constantCoeff_eq]
  constructor
  · intro h s hs hs0
    rw [hs0, mem_support_iff] at hs
    exact hs h
  · intro h
    by_contra h0
    exact h 0 (mem_support_iff.2 h0) rfl

private theorem isMaximal_mX : (mX k d).IsMaximal := by
  rw [← ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ fun r => ⟨C r, constantCoeff_C _ r⟩

private theorem mX_ne_top : mX k d ≠ ⊤ := (isMaximal_mX k d).ne_top

private theorem two_le_degree_iff (s : Fin d →₀ ℕ) :
    2 ≤ Finsupp.degree s ↔ ∃ i j : Fin d, Finsupp.single i 1 + Finsupp.single j 1 ≤ s := by
  constructor
  · intro h2
    have hs0 : s ≠ 0 := by
      intro h; rw [h, map_zero] at h2; omega
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hs0
    have hi' : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    set t := s - Finsupp.single i 1 with ht
    have hst : s = Finsupp.single i 1 + t := (add_tsub_cancel_of_le hi').symm
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hst, h0, add_zero, Finsupp.degree_single] at h2
      omega
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 ht0
    have hj' : Finsupp.single j 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hj)
    exact ⟨i, j, by rw [hst]; exact add_le_add le_rfl hj'⟩
  · rintro ⟨i, j, hij⟩
    obtain ⟨u, hu⟩ := le_iff_exists_add.1 hij
    rw [hu, map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega

private theorem degree_eq_one (s : Fin d →₀ ℕ) (h : Finsupp.degree s = 1) :
    ∃ i : Fin d, s = Finsupp.single i 1 := by
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, map_zero] at h; omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hs0
  have hi' : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
  have hst : s = Finsupp.single i 1 + (s - Finsupp.single i 1) := (add_tsub_cancel_of_le hi').symm
  refine ⟨i, ?_⟩
  have hdeg : Finsupp.degree (s - Finsupp.single i 1) = 0 := by
    rw [hst, map_add, Finsupp.degree_single] at h
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  rw [hst, hdeg, add_zero]

private theorem range_X_mul_range_X :
    (Set.range (X : Fin d → MvPolynomial (Fin d) k)) * Set.range (X : Fin d → MvPolynomial (Fin d) k) =
      (fun s => monomial s (1 : k)) ''
        {u | ∃ i j : Fin d, u = Finsupp.single i 1 + Finsupp.single j 1} := by
  ext f
  simp only [Set.mem_mul, Set.mem_range, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, rfl⟩, by rw [X, X, monomial_mul, one_mul]⟩
  · rintro ⟨_, ⟨i, j, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, by rw [X, X, monomial_mul, one_mul]⟩

private theorem mem_mX_sq_iff (f : MvPolynomial (Fin d) k) :
    f ∈ mX k d ^ 2 ↔ ∀ s ∈ f.support, 2 ≤ Finsupp.degree s := by
  rw [sq, mX, Ideal.span_mul_span', range_X_mul_range_X, mem_ideal_span_monomial_image]
  refine forall₂_congr fun s _ => ?_
  rw [two_le_degree_iff]
  constructor
  · rintro ⟨_, ⟨i, j, rfl⟩, h⟩
    exact ⟨i, j, h⟩
  · rintro ⟨i, j, h⟩
    exact ⟨_, ⟨i, j, rfl⟩, h⟩

private theorem coeff_single_eq_zero_of_mem_sq {f : MvPolynomial (Fin d) k} (hf : f ∈ mX k d ^ 2)
    (i : Fin d) : coeff (Finsupp.single i 1) f = 0 := by
  by_contra h
  have := (mem_mX_sq_iff k d f).1 hf _ (mem_support_iff.2 h)
  rw [Finsupp.degree_single] at this
  omega

private theorem mem_sq_of_coeff_single_eq_zero {f : MvPolynomial (Fin d) k} (hf : f ∈ mX k d)
    (h : ∀ i : Fin d, coeff (Finsupp.single i 1) f = 0) : f ∈ mX k d ^ 2 := by
  rw [mem_mX_sq_iff]
  intro s hs
  by_contra hlt
  have hs0 : s ≠ 0 := (mem_mX_iff k d f).1 hf s hs
  have h1 : Finsupp.degree s = 1 := by
    have : Finsupp.degree s ≠ 0 := fun h0 => hs0 ((Finsupp.degree_eq_zero_iff s).1 h0)
    omega
  obtain ⟨i, rfl⟩ := degree_eq_one d s h1
  exact (mem_support_iff.1 hs) (h i)

private noncomputable def coeffLin : ↥(mX k d) →ₗ[k] (Fin d → k) where
  toFun x := fun i => coeff (Finsupp.single i 1) (x : MvPolynomial (Fin d) k)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp [coeff_smul]

private theorem coeffLin_apply (x : ↥(mX k d)) (i : Fin d) :
    coeffLin k d x i = coeff (Finsupp.single i 1) (x : MvPolynomial (Fin d) k) := rfl

private theorem coeffLin_mul (x y : ↥(mX k d)) : coeffLin k d (x * y) = 0 := by
  funext i
  rw [coeffLin_apply, Pi.zero_apply]
  refine coeff_single_eq_zero_of_mem_sq k d ?_ i
  rw [sq]
  exact Ideal.mul_mem_mul x.2 y.2

private theorem finrank_cotangent_mX : Module.finrank k (mX k d).Cotangent = d := by
  classical
  let L : (mX k d).Cotangent →ₗ[k] (Fin d → k) := Ideal.Cotangent.lift (coeffLin k d) (coeffLin_mul k d)
  have hsurj : Function.Surjective L := by
    rw [Ideal.Cotangent.lift_surjective_iff]
    intro v
    refine ⟨⟨∑ i, v i • X i, Ideal.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨i, rfl⟩)⟩, ?_⟩
    funext j
    rw [coeffLin_apply]
    simp only [coeff_sum, coeff_smul, coeff_X', smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finsupp.single_left_inj Nat.one_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := (mX k d).toCotangent_surjective c
    rw [Ideal.toCotangent_eq_zero]
    have hc' : coeffLin k d x = 0 := by
      rwa [Ideal.Cotangent.lift_toCotangent] at hc
    exact mem_sq_of_coeff_single_eq_zero k d x.2 fun i => by
      rw [← coeffLin_apply, hc', Pi.zero_apply]
  rw [(LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

private theorem exponent_eq_zero {p : ℕ} (hp : 1 < p) (e : Fin d → ℕ) (i : Fin d)
    (h : (X i : MvPolynomial (Fin d) k) ^ p ∈
      Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) k) ^ p ^ (e j + 1))) :
    e i = 0 := by
  classical
  have hS : Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) k) ^ p ^ (e j + 1)) =
      Ideal.span ((fun s => monomial s (1 : k)) ''
        Set.range fun j : Fin d => Finsupp.single j (p ^ (e j + 1))) := by
    rw [← Set.range_comp]
    congr 1
    ext j : 1
    simp [X_pow_eq_monomial]
  rw [hS, mem_ideal_span_monomial_image] at h
  have hsupp : Finsupp.single i p ∈ ((X i : MvPolynomial (Fin d) k) ^ p).support := by
    rw [X_pow_eq_monomial, support_monomial, if_neg one_ne_zero, Finset.mem_singleton]
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := h _ hsupp
  have hji := Finsupp.single_le_iff.1 hj
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same] at hji
    have h1 : p ^ (e i + 1) ≤ p ^ 1 := by rwa [pow_one]
    have := (Nat.pow_le_pow_iff_right hp).1 h1
    omega
  · rw [Finsupp.single_apply, if_neg hij] at hji
    exact absurd hji (not_le.2 (pow_pos (by omega) _))

private theorem truncIdeal_le_mX_sq (m : ℕ) (hm : 2 ≤ m) : truncIdeal k d m ≤ mX k d ^ 2 := by
  rw [truncIdeal]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  have hXi : (X i : MvPolynomial (Fin d) k) ∈ mX k d := Ideal.subset_span (Set.mem_range_self i)
  exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hXi m)

private theorem truncIdeal_le_mX (m : ℕ) (hm : 2 ≤ m) : truncIdeal k d m ≤ mX k d :=
  (truncIdeal_le_mX_sq k d m hm).trans (Ideal.pow_le_self two_ne_zero)

end Poly

section Cot

private theorem finrank_cotangent_eq_of_surjective {k : Type*} [Field k] {A B : Type*} [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (I : Ideal A) (I' : Ideal B) (hI : I = I'.comap f) (hker : RingHom.ker f ≤ I ^ 2) :
    Module.finrank k I.Cotangent = Module.finrank k I'.Cotangent := by
  have h : I ≤ I'.comap f := hI.le
  have hI' : I' = I.map f := by rw [hI, Ideal.map_comap_of_surjective f hf]
  refine (LinearEquiv.ofBijective (Ideal.mapCotangent I I' f h) ⟨?_, ?_⟩).finrank_eq
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective c
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hc
    rw [Ideal.toCotangent_eq_zero]
    change f x ∈ I' ^ 2 at hc
    rw [hI', ← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hker] at hc
    exact hc
  · intro c
    obtain ⟨y, rfl⟩ := I'.toCotangent_surjective c
    obtain ⟨x, hx⟩ := hf y
    have hxI : x ∈ I := by
      rw [hI, Ideal.mem_comap, hx]
      exact y.2
    refine ⟨I.toCotangent ⟨x, hxI⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    congr 1
    exact Subtype.ext hx

end Cot

section Frobenius

variable (p : ℕ) [Fact p.Prime]

private def frobAlg (B : Type*) [CommRing B] [Algebra (ZMod p) B] : B →ₐ[ZMod p] B where
  __ := powMonoidHom p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' x y := by
    nontriviality B
    have : CharP B p := charP_of_injective_algebraMap' (ZMod p) p
    have : ExpChar B p := .prime Fact.out
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, powMonoidHom_apply]
    have h := add_pow_expChar_pow x y p 1
    rwa [pow_one] at h
  commutes' r := by simp [← map_pow, ZMod.pow_card]

variable (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]

private def frobBialg : A →ₐc[ZMod p] A :=
  BialgHom.ofAlgHom (frobAlg p A)
    (by
      ext a
      change Bialgebra.counitAlgHom (ZMod p) A (a ^ p) = Bialgebra.counitAlgHom (ZMod p) A a
      rw [map_pow, ZMod.pow_card])
    (by
      have h : Algebra.TensorProduct.map (frobAlg p A) (frobAlg p A) = frobAlg p (A ⊗[ZMod p] A) := by
        apply Algebra.TensorProduct.ext'
        intro a b
        simp [frobAlg, Algebra.TensorProduct.tmul_pow]
      rw [h]
      ext a
      change (Bialgebra.comulAlgHom (ZMod p) A a) ^ p = Bialgebra.comulAlgHom (ZMod p) A (a ^ p)
      rw [map_pow])

private theorem frobBialg_apply (a : A) : frobBialg p A a = a ^ p := rfl

private theorem map_frobBialg_ker_counit :
    Ideal.map (frobBialg p A : A →ₐ[ZMod p] A) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)) =
      Ideal.span ((fun a : A => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) : Set A)) :=
  rfl

end Frobenius

section Main

open MvPolynomial

private theorem main (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    [Module.Finite (ZMod p) A] :
    Module.finrank (ZMod p) (A ⧸ Ideal.span ((fun a : A => a ^ p) ''
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) : Set A))) =
      p ^ Module.finrank (ZMod p) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)).Cotangent := by
  classical
  have hp : p.Prime := Fact.out
  set I : Ideal A := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) with hIdef
  set J : Ideal A := Ideal.span ((fun a : A => a ^ p) '' (I : Set A)) with hJdef

  obtain ⟨Q, _, _, π, hπ, hker, -, hfin⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_map_ker_counit (frobBialg p A)
  haveI : Module.Finite (ZMod p) Q := hfin inferInstance
  rw [map_frobBialg_ker_counit] at hker
  have hkerA : RingHom.ker (π : A →ₐ[ZMod p] Q) = J := hker
  have hmemJ : ∀ x, x ∈ J ↔ π x = 0 := fun x => by
    rw [← hkerA, RingHom.mem_ker]
    rfl
  set IQ : Ideal Q := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Q) with hIQdef
  have hcounitπ : ∀ a, Coalgebra.counit (R := ZMod p) (π a) = Coalgebra.counit (R := ZMod p) a :=
    fun a => CoalgHomClass.counit_comp_apply π a
  have hIcomap : I = IQ.comap (π : A →ₐ[ZMod p] Q) := by
    ext a
    rw [Ideal.mem_comap, hIdef, hIQdef, RingHom.mem_ker, RingHom.mem_ker]
    change _ ↔ Coalgebra.counit (R := ZMod p) (π a) = 0
    rw [hcounitπ]
    rfl

  have hpow : ∀ t : Q, Coalgebra.counit (R := ZMod p) t = 0 → t ^ p = 0 := by
    intro t ht
    obtain ⟨a, rfl⟩ := hπ t
    rw [hcounitπ] at ht
    have ha : a ^ p ∈ J := Ideal.subset_span ⟨a, ht, rfl⟩
    rw [← map_pow, ← hmemJ]
    exact ha
  have hnil : ∀ x : Q, Coalgebra.counit (R := ZMod p) x = 0 → IsNilpotent x :=
    fun x hx => Exists.intro p (hpow x hx)

  obtain ⟨d, e, ⟨φ⟩⟩ :=
    HopfAlgebra.exists_algEquiv_mvPolynomial_quotient_X_pow_of_isNilpotent (ZMod p) p Q hnil

  have he : ∀ i, e i = 0 := by
    intro i
    set t : Q := φ.symm (Ideal.Quotient.mk _ (X i)) with htdef
    have htnil : IsNilpotent t := by
      refine Exists.intro (p ^ (e i + 1)) ?_
      rw [htdef, ← map_pow, ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
    have hct : Coalgebra.counit (R := ZMod p) t = 0 := by
      have := htnil.map (Bialgebra.counitAlgHom (ZMod p) Q)
      exact this.eq_zero
    have htp : t ^ p = 0 := hpow t hct
    have hX : Ideal.Quotient.mk
        (Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) (ZMod p)) ^ p ^ (e j + 1)))
        ((X i : MvPolynomial (Fin d) (ZMod p)) ^ p) = 0 := by
      rw [map_pow, show Ideal.Quotient.mk _ (X i) = φ t by rw [htdef, AlgEquiv.apply_symm_apply],
        ← map_pow, htp, map_zero]
    exact exponent_eq_zero (ZMod p) d hp.one_lt e i (Ideal.Quotient.eq_zero_iff_mem.1 hX)
  have hMe : Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) (ZMod p)) ^ p ^ (e j + 1)) =
      truncIdeal (ZMod p) d p := by
    have hfun : (fun j : Fin d => (X j : MvPolynomial (Fin d) (ZMod p)) ^ p ^ (e j + 1)) =
        fun j => (X j : MvPolynomial (Fin d) (ZMod p)) ^ p := by
      funext j
      rw [he j, zero_add, pow_one]
    rw [truncIdeal, hfun]
  set M : Ideal (MvPolynomial (Fin d) (ZMod p)) := truncIdeal (ZMod p) d p with hMdef
  let φ' : Q ≃ₐ[ZMod p] MvPolynomial (Fin d) (ZMod p) ⧸ M :=
    φ.trans (Ideal.quotientEquivAlgOfEq (ZMod p) hMe)
  let ψ : Q →ₐ[ZMod p] MvPolynomial (Fin d) (ZMod p) ⧸ M := φ'
  have hψ : ∀ t, ψ t = φ' t := fun _ => rfl

  have hrank : Module.finrank (ZMod p) (A ⧸ J) = p ^ d := by
    have eA : (A ⧸ J) ≃ₐ[ZMod p] Q :=
      (Ideal.quotientEquivAlgOfEq (ZMod p) hkerA.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
    rw [eA.toLinearEquiv.finrank_eq, φ'.toLinearEquiv.finrank_eq]
    exact (finite_and_finrank_quotient_truncIdeal (ZMod p) d p).2

  set m' : Ideal (MvPolynomial (Fin d) (ZMod p) ⧸ M) :=
    (mX (ZMod p) d).map (Ideal.Quotient.mk M) with hm'def
  have hMle : M ≤ mX (ZMod p) d := truncIdeal_le_mX (ZMod p) d p hp.two_le
  have hcomap_mk : mX (ZMod p) d = m'.comap (Ideal.Quotient.mkₐ (ZMod p) M) := by
    rw [hm'def]
    change _ = Ideal.comap (Ideal.Quotient.mk M) (Ideal.map (Ideal.Quotient.mk M) (mX (ZMod p) d))
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hMle]
  have hm'ne : m' ≠ ⊤ := by
    intro htop
    apply mX_ne_top (ZMod p) d
    rw [hcomap_mk, htop, Ideal.comap_top]

  have h2 : Module.finrank (ZMod p) (mX (ZMod p) d).Cotangent = Module.finrank (ZMod p) m'.Cotangent := by
    refine finrank_cotangent_eq_of_surjective (Ideal.Quotient.mkₐ (ZMod p) M)
      (Ideal.Quotient.mkₐ_surjective _ _) _ _ hcomap_mk ?_
    have : RingHom.ker (Ideal.Quotient.mkₐ (ZMod p) M) = M := Ideal.mk_ker
    rw [this]
    exact truncIdeal_le_mX_sq (ZMod p) d p hp.two_le

  have hIQmax : IQ.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom (ZMod p) Q) fun r =>
      ⟨algebraMap (ZMod p) Q r, (Bialgebra.counitAlgHom (ZMod p) Q).commutes r⟩
  have hIQcomap : IQ = m'.comap ψ := by
    refine hIQmax.eq_of_le (Ideal.comap_ne_top _ hm'ne) fun t ht => ?_
    rw [Ideal.mem_comap]
    have htp : ψ t ^ p = 0 := by
      rw [← map_pow, hpow t ht, map_zero]
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (ψ t)
    rw [← hf] at htp ⊢
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at htp
    have hfm : f ∈ mX (ZMod p) d := (isMaximal_mX (ZMod p) d).isPrime.mem_of_pow_mem p (hMle htp)
    exact Ideal.mem_map_of_mem _ hfm
  have h3 : Module.finrank (ZMod p) IQ.Cotangent = Module.finrank (ZMod p) m'.Cotangent := by
    refine finrank_cotangent_eq_of_surjective ψ φ'.surjective _ _ hIQcomap ?_
    intro x hx
    rw [RingHom.mem_ker, hψ] at hx
    have : x = 0 := φ'.injective (by rw [map_zero]; exact hx)
    rw [this]
    exact Ideal.zero_mem _

  have h1 : Module.finrank (ZMod p) I.Cotangent = Module.finrank (ZMod p) IQ.Cotangent := by
    refine finrank_cotangent_eq_of_surjective (π : A →ₐ[ZMod p] Q) hπ _ _ hIcomap ?_
    rw [hkerA, hJdef]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Ideal.pow_le_pow_right hp.two_le (Ideal.pow_mem_pow ha p)
  rw [hrank, h1, h3, ← h2, finrank_cotangent_mX]

end Main

end HopfAlgebra.KerFrobC12

theorem solution
    (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    [Module.Finite (ZMod p) A] :
    Module.finrank (ZMod p) (A ⧸ Ideal.span ((fun a : A => a ^ p) ''
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) : Set A))) =
      p ^ Module.finrank (ZMod p) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)).Cotangent :=
  HopfAlgebra.KerFrobC12.main p A

end S_HopfAlgebra_finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent
end P2MW
export P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent (solution)
