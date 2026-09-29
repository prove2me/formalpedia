-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_quotient_of_forall_fixing_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8e5f2f3a-db64-5431-a76b-2883dc826052

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem

open scoped TensorProduct

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace DESCKDN

section AntipodeAlgHom

variable (R A : Type) [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

noncomputable def antipodeAlgHom : A →ₐ[R] A where
  toFun := HopfAlgebra.antipode R
  map_one' := HopfAlgebra.antipode_one
  map_mul' a b := by rw [HopfAlgebra.antipode_mul, mul_comm]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one]

@[scoped simp]
lemma antipodeAlgHom_apply (a : A) :
    antipodeAlgHom R A a = HopfAlgebra.antipode R a := rfl

end AntipodeAlgHom

section ConvInverse

variable {R A L : Type} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing L] [Algebra R L]

private lemma lmul_map_eq (φ : A →ₐ[R] L) (z : A ⊗[R] A) :
    Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map φ (φ.comp (antipodeAlgHom R A)) z)
    = φ (LinearMap.mul' R A (LinearMap.lTensor A (HopfAlgebra.antipode R) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        LinearMap.lTensor_tmul, LinearMap.mul'_apply, map_mul, AlgHom.comp_apply,
        antipodeAlgHom_apply]
  | add y z ihy ihz =>
      simp only [map_add, ihy, ihz]

theorem toConv_mul_toConv_comp_antipodeAlgHom (φ : A →ₐ[R] L) :
    WithConv.toConv φ * WithConv.toConv (φ.comp (antipodeAlgHom R A)) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  show Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map φ (φ.comp (antipodeAlgHom R A))
        (Bialgebra.comulAlgHom R A x))
    = algebraMap R L (Coalgebra.counit x)
  rw [Bialgebra.comulAlgHom_apply, lmul_map_eq φ (Coalgebra.comul x)]
  rw [HopfAlgebra.mul_antipode_lTensor_comul_apply]
  exact φ.commutes _

end ConvInverse

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

namespace DESCKDN

section Descent

open IntermediateField

theorem exists_mul_eq_of_forall_fixing (O : Subring (AlgebraicClosure ℚ))
    (x : AlgebraicClosure ℚ)
    (hx : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ a ∈ O, σ a = a) → σ x = x) :
    ∃ a b : ↥O, b ≠ 0 ∧ (b : AlgebraicClosure ℚ) * x = a := by
  classical
  set FO : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (O : Set (AlgebraicClosure ℚ)) with hFO
  have hxFO : x ∈ FO := by
    rw [hFO, ← InfiniteGalois.fixedField_fixingSubgroup
      (IntermediateField.adjoin ℚ (O : Set (AlgebraicClosure ℚ)))]
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ a ∈ O, σ a = a := by
      intro a ha
      have haFO : (a : AlgebraicClosure ℚ) ∈
          IntermediateField.adjoin ℚ (O : Set (AlgebraicClosure ℚ)) :=
        IntermediateField.subset_adjoin _ _ ha
      simp only [IntermediateField.mem_fixingSubgroup_iff] at hσ
      exact hσ _ haFO
    exact hx σ hfix
  clear hx
  induction hxFO using IntermediateField.adjoin_induction with
  | mem y hy => exact ⟨⟨y, hy⟩, 1, one_ne_zero, by simp⟩
  | algebraMap q =>
      refine ⟨⟨(q.num : AlgebraicClosure ℚ), intCast_mem O q.num⟩,
        ⟨(q.den : AlgebraicClosure ℚ), natCast_mem O q.den⟩, ?_, ?_⟩
      · intro h0
        have h1 : ((q.den : ℕ) : AlgebraicClosure ℚ) = 0 := congrArg Subtype.val h0
        have h2 : (q.den : ℕ) = 0 := by exact_mod_cast h1
        exact q.den_nz h2
      · show ((q.den : AlgebraicClosure ℚ)) * algebraMap ℚ (AlgebraicClosure ℚ) q
            = ((q.num : AlgebraicClosure ℚ))
        have hden : ((q.den : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast q.den_nz
        have hQ : ((q.den : ℕ) : ℚ) * q = ((q.num : ℤ) : ℚ) := by
          rw [mul_comm]
          exact ((div_eq_iff hden).mp (Rat.num_div_den q)).symm
        have h2 := congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) hQ
        rw [map_mul, map_natCast, map_intCast] at h2
        exact h2
  | add y z hy hz ihy ihz =>
      obtain ⟨a₁, b₁, hb₁, he₁⟩ := ihy
      obtain ⟨a₂, b₂, hb₂, he₂⟩ := ihz
      refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
      push_cast
      calc ((b₁ : AlgebraicClosure ℚ) * b₂) * (y + z)
          = (b₂ : AlgebraicClosure ℚ) * ((b₁ : AlgebraicClosure ℚ) * y)
            + (b₁ : AlgebraicClosure ℚ) * ((b₂ : AlgebraicClosure ℚ) * z) := by ring
        _ = (a₁ : AlgebraicClosure ℚ) * b₂ + (a₂ : AlgebraicClosure ℚ) * b₁ := by
            rw [he₁, he₂]; ring
  | inv y hy ihy =>
      obtain ⟨a, b, hb, he⟩ := ihy
      by_cases hy0 : y = 0
      · exact ⟨0, 1, one_ne_zero, by simp [hy0]⟩
      · have hbQ : (b : AlgebraicClosure ℚ) ≠ 0 := by
          exact_mod_cast hb
        have ha0 : a ≠ 0 := by
          intro h0
          apply hy0
          have hby : (b : AlgebraicClosure ℚ) * y = 0 := by
            rw [he, h0]
            simp
          exact (mul_eq_zero.mp hby).resolve_left hbQ
        have haQ : (a : AlgebraicClosure ℚ) ≠ 0 := by
          exact_mod_cast ha0
        refine ⟨b, a, ha0, ?_⟩
        field_simp
        rw [← he]
        ring
  | mul y z hy hz ihy ihz =>
      obtain ⟨a₁, b₁, hb₁, he₁⟩ := ihy
      obtain ⟨a₂, b₂, hb₂, he₂⟩ := ihz
      refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
      push_cast
      calc ((b₁ : AlgebraicClosure ℚ) * b₂) * (y * z)
          = ((b₁ : AlgebraicClosure ℚ) * y) * ((b₂ : AlgebraicClosure ℚ) * z) := by ring
        _ = (a₁ : AlgebraicClosure ℚ) * a₂ := by rw [he₁, he₂]

end Descent
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

section Averaging

variable (O : Subring (AlgebraicClosure ℚ))

def fixingLinearMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ a ∈ O, σ a = a) : AlgebraicClosure ℚ →ₗ[↥O] AlgebraicClosure ℚ where
  toFun := σ
  map_add' := map_add σ
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    have halg : algebraMap (↥O) (AlgebraicClosure ℚ) r = (r : AlgebraicClosure ℚ) := rfl
    rw [Algebra.smul_def, Algebra.smul_def, halg, map_mul, hσ r r.2]

variable {O}

theorem exists_smul_eq_one_tmul_of_forall_fixing {G : Type} [AddCommGroup G]
    [Module ↥O G] [Module.Free ↥O G] [Module.Finite ↥O G]
    (z : (AlgebraicClosure ℚ) ⊗[↥O] G)
    (hz : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : ∀ a ∈ O, σ a = a),
      LinearMap.rTensor G (fixingLinearMap O σ hσ) z = z) :
    ∃ (r : ↥O) (g : G), r ≠ 0 ∧ r • z = (1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] g := by
  classical
  haveI : Nontrivial ↥O := ⟨0, 1, by
    intro h01
    have := congrArg (Subtype.val) h01
    simp at this⟩

  let ι := Module.Free.ChooseBasisIndex ↥O G
  let b : Module.Basis ι ↥O G := Module.Free.chooseBasis ↥O G
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ↥O G
  let b' : Module.Basis ι (AlgebraicClosure ℚ) ((AlgebraicClosure ℚ) ⊗[↥O] G) :=
    b.baseChange (AlgebraicClosure ℚ)

  have hcoord : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (hσ : ∀ a ∈ O, σ a = a) (i : ι), σ (b'.repr z i) = b'.repr z i := by
    intro σ hσ i
    have hmap : LinearMap.rTensor G (fixingLinearMap O σ hσ) z
        = Finsupp.sum (b'.repr z) (fun j c => σ c • b' j) := by
      conv_lhs => rw [← b'.linearCombination_repr z]
      rw [Finsupp.linearCombination_apply, map_finsuppSum]
      congr 1
      ext j c
      show LinearMap.rTensor G (fixingLinearMap O σ hσ) (c • b' j) = σ c • b' j
      have hb : (b' j : (AlgebraicClosure ℚ) ⊗[↥O] G)
          = (1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (b j) := by
        simp [b']
      rw [hb]
      have hsm : c • ((1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (b j)) = c ⊗ₜ[↥O] (b j) := by
        rw [TensorProduct.smul_tmul']
        congr 1
        exact mul_one c
      rw [hsm, LinearMap.rTensor_tmul]
      show (σ c) ⊗ₜ[↥O] (b j) = σ c • ((1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (b j))
      rw [TensorProduct.smul_tmul']
      congr 1
      exact (mul_one (σ c)).symm
    have hz' := hz σ hσ
    rw [hmap] at hz'
    have hrepr := congrArg (fun w => b'.repr w i) hz'
    simp only [map_finsuppSum, Finsupp.sum_apply] at hrepr

    rw [Finsupp.sum_eq_single i (fun j c hji => by
        simp [Module.Basis.repr_self, hji]) (by simp)] at hrepr
    simpa [Module.Basis.repr_self] using hrepr

  have hfrac : ∀ i : ι, ∃ a r : ↥O, r ≠ 0 ∧
      (r : AlgebraicClosure ℚ) * (b'.repr z i) = a := by
    intro i
    exact exists_mul_eq_of_forall_fixing O (b'.repr z i)
      (fun σ hσ => hcoord σ hσ i)
  choose av rv hrv hev using hfrac

  set r : ↥O := ∏ i, rv i with hr
  have hrne : r ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hrv i)
  refine ⟨r, ∑ i, ((∏ j ∈ Finset.univ.erase i, rv j) * av i) • b i, hrne, ?_⟩

  conv_lhs => rw [← b'.linearCombination_repr z]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.smul_sum]
  rw [Finsupp.sum_fintype _ _ (by intro i; rw [zero_smul, smul_zero])]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _

  have hb : (b' i : (AlgebraicClosure ℚ) ⊗[↥O] G)
      = (1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (b i) := by
    simp [b']
  have hsm : (b'.repr z i) • (b' i) = (b'.repr z i) ⊗ₜ[↥O] (b i) := by
    rw [hb, TensorProduct.smul_tmul']
    congr 1
    exact mul_one _
  rw [hsm]
  have hscal : r • ((b'.repr z i) ⊗ₜ[↥O] (b i))
      = ((r : AlgebraicClosure ℚ) * b'.repr z i) ⊗ₜ[↥O] (b i) := by
    rw [TensorProduct.smul_tmul']
    congr 1
  rw [hscal]
  have hcoeff : (r : AlgebraicClosure ℚ) * b'.repr z i
      = ((((∏ j ∈ Finset.univ.erase i, rv j) * av i : ↥O)) : AlgebraicClosure ℚ) := by
    have h1 : (r : AlgebraicClosure ℚ)
        = (((∏ j ∈ Finset.univ.erase i, rv j : ↥O)) : AlgebraicClosure ℚ)
          * ((rv i : ↥O) : AlgebraicClosure ℚ) := by
      rw [hr]
      norm_cast
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [h1, mul_assoc, hev i]
    norm_cast
  rw [hcoeff]
  have ho : ∀ (o : ↥O) (g : G), ((o : AlgebraicClosure ℚ)) ⊗ₜ[↥O] g
      = (1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (o • g) := by
    intro o g
    calc ((o : AlgebraicClosure ℚ)) ⊗ₜ[↥O] g
        = (o • (1 : AlgebraicClosure ℚ)) ⊗ₜ[↥O] g := by
          have halg : algebraMap (↥O) (AlgebraicClosure ℚ) o = (o : AlgebraicClosure ℚ) := rfl
          rw [Algebra.smul_def, halg, mul_one]
      _ = (1 : AlgebraicClosure ℚ) ⊗ₜ[↥O] (o • g) := TensorProduct.smul_tmul o 1 g
  exact ho _ _

end Averaging
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

namespace DESCKDN
section Glue

local notation "Qb" => AlgebraicClosure ℚ

variable (O : Subring Qb)

def permPoint (σ : Qb ≃ₐ[ℚ] Qb) (hσ : ∀ a ∈ O, σ a = a)
    {G : Type} [CommRing G] [Algebra ↥O G] (k : G →ₐ[↥O] Qb) : G →ₐ[↥O] Qb where
  toFun x := σ (k x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]
  commutes' r := by rw [k.commutes]; exact hσ r r.2

lemma permPoint_apply (σ : Qb ≃ₐ[ℚ] Qb) (hσ : ∀ a ∈ O, σ a = a)
    {G : Type} [CommRing G] [Algebra ↥O G] (k : G →ₐ[↥O] Qb) (x : G) :
    permPoint O σ hσ k x = σ (k x) := rfl

lemma permPoint_injective (σ : Qb ≃ₐ[ℚ] Qb) (hσ : ∀ a ∈ O, σ a = a)
    {G : Type} [CommRing G] [Algebra ↥O G] :
    Function.Injective (permPoint O σ hσ (G := G)) := by
  intro k k' hkk'
  ext x
  exact σ.injective (DFunLike.congr_fun hkk' x)

lemma rTensor_fixingLinearMap_lTrans (σ : Qb ≃ₐ[ℚ] Qb) (hσ : ∀ a ∈ O, σ a = a)
    {G : Type} [CommRing G] [Bialgebra ↥O G] (k : G →ₐ[↥O] Qb) (g : G) :
    LinearMap.rTensor G (fixingLinearMap O σ hσ)
      ((Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp (Bialgebra.comulAlgHom ↥O G) g)
    = (Algebra.TensorProduct.map (permPoint O σ hσ k) (AlgHom.id ↥O G)).comp
        (Bialgebra.comulAlgHom ↥O G) g := by
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  set 𝓡 := Coalgebra.Repr.arbitrary (↥O) g
  rw [← 𝓡.eq]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul]
  rfl

end Glue
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"
end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

namespace DESCKDN

section EPrime

open WithConv

variable {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
variable {G : Type} [CommRing G] [Bialgebra R G] {H : Type} [CommRing H] [Bialgebra R H]
variable {N : Type} [AddCommGroup N]

theorem exists_equiv_quotient_of_fibre (D' : AddSubgroup N)
    (e : WithConv (G →ₐ[R] L) ≃ N) (he_add : ∀ f g, e (f * g) = e f + e g)
    (K : Finset (G →ₐ[R] L)) (hK : ∀ k, k ∈ K ↔ e (toConv k) ∈ D')
    (ι : H →ₐc[R] G)
    (hSurj : Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H →ₐ[R] G)))
    (hFib : ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H →ₐ[R] G) = ψ.comp (ι : H →ₐ[R] G) ↔
      ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ)) :
    ∃ e' : WithConv (H →ₐ[R] L) ≃ N ⧸ D',
      (∀ x y, e' (x * y) = e' x + e' y) ∧
      ∀ φ : WithConv (G →ₐ[R] L),
        e' (WithConv.toConv ((WithConv.ofConv φ).comp (ι : H →ₐ[R] G)))
          = QuotientAddGroup.mk (e φ) := by
  classical

  let res : WithConv (G →ₐ[R] L) → WithConv (H →ₐ[R] L) :=
    fun φ => toConv ((ofConv φ).comp (ι : H →ₐ[R] G))
  have hres_mul : ∀ φ ψ, res (φ * ψ) = res φ * res ψ := fun φ ψ => by
    show toConv ((ofConv (φ * ψ)).comp (ι : H →ₐ[R] G))
      = toConv ((ofConv φ).comp (ι : H →ₐ[R] G)) * toConv ((ofConv ψ).comp (ι : H →ₐ[R] G))
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]
  have hres_surj : Function.Surjective res := fun χ => by
    obtain ⟨φ, hφ⟩ := hSurj (ofConv χ)
    have hφ' : φ.comp (ι : H →ₐ[R] G) = ofConv χ := hφ
    refine ⟨toConv φ, ?_⟩
    show toConv ((ofConv (toConv φ)).comp (ι : H →ₐ[R] G)) = χ
    rw [ofConv_toConv, hφ', toConv_ofConv]
  have hres_fib : ∀ φ ψ, res φ = res ψ ↔ ∃ k ∈ K, ψ = toConv k * φ := fun φ ψ => by
    constructor
    · intro h
      obtain ⟨k, hk, hkψ⟩ := (hFib (ofConv φ) (ofConv ψ)).mp (WithConv.toConv_injective h)
      refine ⟨k, hk, WithConv.ofConv_injective ?_⟩
      rw [hkψ, toConv_ofConv]
    · rintro ⟨k, hk, rfl⟩
      exact congrArg toConv ((hFib (ofConv φ) (ofConv (toConv k * φ))).mpr
        ⟨k, hk, by rw [toConv_ofConv]⟩)

  let s : WithConv (H →ₐ[R] L) → WithConv (G →ₐ[R] L) := Function.surjInv hres_surj
  have hs : ∀ χ, res (s χ) = χ := Function.surjInv_eq hres_surj
  let f : WithConv (H →ₐ[R] L) → N ⧸ D' := fun χ => QuotientAddGroup.mk (e (s χ))
  have hf_res : ∀ φ, f (res φ) = QuotientAddGroup.mk (e φ) := fun φ => by
    obtain ⟨k, hk, hkφ⟩ := (hres_fib φ (s (res φ))).mp (hs (res φ)).symm
    show QuotientAddGroup.mk (e (s (res φ))) = QuotientAddGroup.mk (e φ)
    rw [hkφ, he_add, QuotientAddGroup.eq_iff_sub_mem, add_sub_cancel_right]
    exact (hK k).mp hk
  have hinj : Function.Injective f := by
    intro χ₁ χ₂ h12
    have h12' : e (s χ₁) - e (s χ₂) ∈ D' := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      exact h12
    have hk : ofConv (e.symm (e (s χ₁) - e (s χ₂))) ∈ K := by
      rw [hK, toConv_ofConv, Equiv.apply_symm_apply]
      exact h12'
    have hmul : s χ₁ = toConv (ofConv (e.symm (e (s χ₁) - e (s χ₂)))) * s χ₂ := by
      apply e.injective
      rw [he_add, toConv_ofConv, Equiv.apply_symm_apply, sub_add_cancel]
    have h := (hres_fib (s χ₂) (s χ₁)).mpr ⟨_, hk, hmul⟩
    rw [hs, hs] at h
    exact h.symm
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨res (e.symm n), by rw [hf_res, Equiv.apply_symm_apply]⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, fun φ => hf_res φ⟩
  intro x y
  obtain ⟨φ, rfl⟩ := hres_surj x
  obtain ⟨ψ, rfl⟩ := hres_surj y
  show f (res φ * res ψ) = f (res φ) + f (res ψ)
  rw [← hres_mul, hf_res, hf_res, hf_res, he_add, QuotientAddGroup.mk_add]

end EPrime
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

end DESCKDN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

open DESCKDN WithConv

theorem solution
    (O : Subring (AlgebraicClosure ℚ)) [IsPrincipalIdealRing ↥O]
    (G : Type) [CommRing G] [HopfAlgebra ↥O G]
    [Module.Finite ↥O G] [Module.Flat ↥O G] [Coalgebra.IsCocomm ↥O G]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ O, σ x = x) →
      ∀ f g : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ),
        (∀ x : G, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (D : AddSubgroup J)
    (hD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ O, σ x = x) →
      ∀ y ∈ M, y ∈ D → σ • y ∈ D) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ↥O H'),
      Module.Finite ↥O H' ∧ Module.Flat ↥O H' ∧ Coalgebra.IsCocomm ↥O H' ∧
      ∃ (ι : H' →ₐc[↥O] G)
        (e' : WithConv (H' →ₐ[↥O] AlgebraicClosure ℚ) ≃ ↥M ⧸ D.addSubgroupOf M),
        (∀ x y, e' (x * y) = e' x + e' y) ∧
        ∀ φ : WithConv (G →ₐ[↥O] AlgebraicClosure ℚ),
          e' (WithConv.toConv ((WithConv.ofConv φ).comp (ι : H' →ₐ[↥O] G)))
            = QuotientAddGroup.mk (e φ) := by
  classical
  set Qb := AlgebraicClosure ℚ

  have hRL : Function.Injective (algebraMap ↥O Qb) := Subtype.val_injective
  haveI hFree : Module.Free ↥O G := Module.free_of_finite_type_torsion_free'

  haveI hFinPts : Finite (G →ₐ[↥O] Qb) := inferInstance
  haveI : Fintype (G →ₐ[↥O] Qb) := Fintype.ofFinite _
  let K : Finset (G →ₐ[↥O] Qb) :=
    Set.toFinset {k | ((e (toConv k) : ↥M) : J) ∈ D}
  have hmemK : ∀ k, k ∈ K ↔ ((e (toConv k) : ↥M) : J) ∈ D := fun k => by
    simp only [K, Set.mem_toFinset, Set.mem_setOf_eq]

  have he_one : e 1 = 0 := by
    have h := he_add 1 1; rw [one_mul] at h
    exact add_right_cancel (a := e 1) (by rw [← h, zero_add])

  have hKone : (Algebra.ofId ↥O Qb).comp (Bialgebra.counitAlgHom ↥O G) ∈ K := by
    rw [hmemK]
    have h1 : toConv ((Algebra.ofId ↥O Qb).comp (Bialgebra.counitAlgHom ↥O G))
        = (1 : WithConv (G →ₐ[↥O] Qb)) := rfl
    rw [h1, he_one]
    exact D.zero_mem

  have hKmul : ∀ k ∈ K, ∀ k' ∈ K, ofConv (toConv k * toConv k') ∈ K := by
    intro k hk k' hk'
    rw [hmemK] at hk hk' ⊢
    rw [toConv_ofConv, he_add]
    exact D.add_mem hk hk'

  have hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode ↥O := by
    intro k hk
    refine ⟨k.comp (antipodeAlgHom ↥O G), ?_, ?_⟩
    · rw [hmemK] at hk ⊢
      have hinv := toConv_mul_toConv_comp_antipodeAlgHom (R := ↥O) (L := Qb) k
      have hsum := he_add (toConv k) (toConv (k.comp (antipodeAlgHom ↥O G)))
      rw [hinv, he_one] at hsum
      have heq : ((e (toConv (k.comp (antipodeAlgHom ↥O G))) : ↥M) : J)
          = -((e (toConv k) : ↥M) : J) := by
        have hJ : ((e (toConv k) : ↥M) : J)
            + ((e (toConv (k.comp (antipodeAlgHom ↥O G))) : ↥M) : J) = 0 := by
          have := congrArg (fun m : ↥M => (m : J)) hsum
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero] at this
          exact this.symm
        exact eq_neg_of_add_eq_zero_right hJ
      rw [heq]
      exact D.neg_mem hk
    · ext x; rfl

  have hdesc : ∀ g : G, ∃ (r : ↥O) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp
        (Bialgebra.comulAlgHom ↥O G) g) = (1 : Qb) ⊗ₜ[↥O] g' := by
    intro g
    set z := ∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp
        (Bialgebra.comulAlgHom ↥O G) g with hz
    apply exists_smul_eq_one_tmul_of_forall_fixing z
    intro σ hσ

    rw [hz, map_sum]
    have hperm : ∀ k ∈ K, permPoint O σ hσ k ∈ K := by
      intro k hk
      rw [hmemK] at hk ⊢
      have hact := he_act σ hσ (toConv k) (toConv (permPoint O σ hσ k))
        (fun x => rfl)
      rw [hact]
      exact hD σ hσ _ (e (toConv k)).2 hk
    have himage : K.image (permPoint O σ hσ) = K := by
      apply Finset.eq_of_subset_of_card_le
      · intro k' hk'
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
        exact hperm k hk
      · rw [Finset.card_image_of_injective K (permPoint_injective O σ hσ)]
    calc ∑ k ∈ K, LinearMap.rTensor G (fixingLinearMap O σ hσ)
            ((Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp
              (Bialgebra.comulAlgHom ↥O G) g)
        = ∑ k ∈ K, (Algebra.TensorProduct.map (permPoint O σ hσ k)
              (AlgHom.id ↥O G)).comp (Bialgebra.comulAlgHom ↥O G) g :=
          Finset.sum_congr rfl (fun k _ => rTensor_fixingLinearMap_lTrans O σ hσ k g)
      _ = ∑ k ∈ K.image (permPoint O σ hσ),
              (Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp
                (Bialgebra.comulAlgHom ↥O G) g :=
          (Finset.sum_image (f := fun k => (Algebra.TensorProduct.map k
              (AlgHom.id ↥O G)).comp (Bialgebra.comulAlgHom ↥O G) g)
            ((permPoint_injective O σ hσ).injOn)).symm
      _ = ∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id ↥O G)).comp
              (Bialgebra.comulAlgHom ↥O G) g := by rw [himage]

  obtain ⟨H', hCR, hHA, hFin', hFlat', hCoc', ι, hSurj, hFib⟩ :=
    HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
      hRL G K hKone hKmul hKS hdesc
  refine ⟨H', hCR, hHA, hFin', hFlat', hCoc', ι, ?_⟩

  exact exists_equiv_quotient_of_fibre (D.addSubgroupOf M) e he_add K
    (fun k => (hmemK k).trans AddSubgroup.mem_addSubgroupOf.symm) ι hSurj hFib
end
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem.DESCKDN"

end S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem (solution)
