-- Prove2me | solution 1 for Matrix.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e101bfdf-6566-537e-9aa5-a5a1d286637d

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

open IsDedekindDomain NumberField

namespace Ws50W2a

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_isUnit_conj_integral
    (O : Subring (Matrix (Fin 2) (Fin 2) K))
    (hsmul : ∀ r : R, ∀ x ∈ O, r • x ∈ O)
    (d : R) (hd : d ≠ 0) (hbdd : ∀ x ∈ O, ∀ i j, ∃ r : R, algebraMap R K r = algebraMap R K d * x i j) :
    ∃ h : Matrix (Fin 2) (Fin 2) K, IsUnit h ∧ ∀ x ∈ O, ∀ i j, ∃ r : R,
      algebraMap R K r = (h⁻¹ * x * h) i j := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdK : algebraMap R K d ≠ 0 := fun h0 => hd (hinj (h0.trans (map_zero _).symm))

  let gen : Set (Fin 2 → K) := {y | ∃ x ∈ O, ∃ i : Fin 2, y = x.mulVec (Pi.single i 1)}
  let L : Submodule R (Fin 2 → K) := Submodule.span R gen
  have hgenL : ∀ x ∈ O, ∀ i, x.mulVec (Pi.single i 1) ∈ L := fun x hx i => Submodule.subset_span ⟨x, hx, i, rfl⟩
  have heL : ∀ i : Fin 2, (Pi.single i (1 : K) : Fin 2 → K) ∈ L := by
    intro i
    have := hgenL 1 O.one_mem i
    rwa [Matrix.one_mulVec] at this

  have hstab : ∀ x ∈ O, ∀ y ∈ L, x.mulVec y ∈ L := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', i, rfl⟩ := hy
      rw [Matrix.mulVec_mulVec]
      exact hgenL _ (O.mul_mem hx hx') i
    | zero => rw [Matrix.mulVec_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact L.add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul K r y, Matrix.mulVec_smul, algebraMap_smul]
      exact L.smul_mem r hy

  let N : Submodule R (Fin 2 → K) :=
    Submodule.span R (Set.range fun j : Fin 2 => ((algebraMap R K d)⁻¹ • Pi.single j (1 : K) : Fin 2 → K))
  have hLN : L ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, i, rfl⟩
    have hcol : x.mulVec (Pi.single i 1) = ∑ j, x j i • (Pi.single j (1 : K) : Fin 2 → K) := by
      ext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    rw [hcol]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := hbdd x hx j i
    have : x j i • (Pi.single j (1 : K) : Fin 2 → K) = r • ((algebraMap R K d)⁻¹ • Pi.single j (1 : K)) := by
      rw [← algebraMap_smul K r, smul_smul, hr, mul_comm, ← mul_assoc, inv_mul_cancel₀ hdK, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hLfg : L.FG := by
    haveI : IsNoetherian R N := isNoetherian_of_fg_of_noetherian _ hNfg
    have h1 : (L.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 : (L.comap N.subtype).map N.subtype = L := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hLN]
    rw [← h2]
    exact h1.map _
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hLfg
  haveI : Module.Free R L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex R L
  let b : Module.Basis ι R L := Module.Free.chooseBasis R L

  let col : ι → (Fin 2 → K) := fun i => (b i : Fin 2 → K)

  have hli : LinearIndependent K col := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨⟨s, hs⟩, hsc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
    choose r hr using hsc
    have hr' : ∀ i, algebraMap R K (r i) = algebraMap R K s * c i := fun i => by
      have h := hr i
      rw [Algebra.smul_def] at h
      exact h
    have hsum : (∑ i, r i • b i : L) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      have : (∑ i, ((r i • b i : L) : Fin 2 → K)) = (algebraMap R K s) • ∑ i, c i • col i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, ← algebraMap_smul K (r i), hr' i, smul_smul]
      rw [this, hc, smul_zero]
    have hri : r i = 0 := by
      have := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at this
      exact this r hsum i
    have hs0 : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have : algebraMap R K s * c i = 0 := by
      have h := hr' i
      rw [hri, map_zero] at h
      exact h.symm
    exact (mul_eq_zero.mp this).resolve_left hs0

  have hsp : ⊤ ≤ Submodule.span K (Set.range col) := by
    have hLle : ∀ y ∈ L, y ∈ Submodule.span K (Set.range col) := by
      intro y hy
      have : y = ∑ i, (b.repr ⟨y, hy⟩ i) • col i := by
        have h := congrArg (fun z : L => (z : Fin 2 → K)) (b.sum_repr ⟨y, hy⟩).symm
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h
      rw [this]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← (Pi.basisFun K (Fin 2)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact hLle _ (heL j)
  let B : Module.Basis ι K (Fin 2 → K) := Module.Basis.mk hli hsp
  have hcard : Fintype.card ι = 2 := by
    have := Module.finrank_eq_card_basis B
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard

  let h : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => col (e.symm j) i
  have hcols : LinearIndependent K (fun j => h.transpose j) := by
    have : (fun j => h.transpose j) = col ∘ e.symm := by
      funext j; ext i; rfl
    rw [this]
    exact hli.comp _ e.symm.injective
  have hU : IsUnit h := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  refine ⟨h, hU, fun x hx i j => ?_⟩

  let C : Matrix (Fin 2) (Fin 2) R := Matrix.of fun k j => b.repr ⟨x.mulVec (col (e.symm j)), hstab x hx _ (b (e.symm j)).2⟩ (e.symm k)
  have hxh : x * h = h * C.map (algebraMap R K) := by
    ext i' j'
    have hrepr := congrArg (fun z : L => (z : Fin 2 → K) i')
      (b.sum_repr ⟨x.mulVec (col (e.symm j')), hstab x hx _ (b (e.symm j')).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at hrepr

    have hl : (x * h) i' j' = (x.mulVec (col (e.symm j'))) i' := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, h]
    rw [hl, ← hrepr, Matrix.mul_apply]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.map_apply, h, C, Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
    ring
  refine ⟨C i j, ?_⟩
  rw [Matrix.mul_assoc, hxh, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.one_mul, Matrix.map_apply]

end PID

section Local

open scoped TensorProduct Quaternion Pointwise

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
    (v : HeightOneSpectrum (𝓞 ℚ))
    (O : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hsmul : ∀ r : v.adicCompletion ℚ, r ∈ v.adicCompletionIntegers ℚ → ∀ x ∈ O, r • x ∈ O)
    (hbdd : ∃ d : v.adicCompletion ℚ, d ≠ 0 ∧ ∀ x ∈ O, ∀ i j, d * x i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ x ∈ O, ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * x *
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by
  set R := v.adicCompletionIntegers ℚ with hR

  obtain ⟨dR, hdR, hbddR⟩ : ∃ dR : R, dR ≠ 0 ∧ ∀ x ∈ O, ∀ i j, ∃ r : R,
      algebraMap R (v.adicCompletion ℚ) r = algebraMap R (v.adicCompletion ℚ) dR * x i j := by
    obtain ⟨d, hd, hbd⟩ := hbdd
    by_cases hdZ : d ∈ v.adicCompletionIntegers ℚ
    · refine ⟨⟨d, hdZ⟩, fun h0 => hd (congrArg Subtype.val h0), fun x hx i j => ⟨⟨d * x i j, hbd x hx i j⟩, rfl⟩⟩
    · have hdinv : d⁻¹ ∈ v.adicCompletionIntegers ℚ :=
        ((v.adicCompletionIntegers ℚ).mem_or_inv_mem d).resolve_left hdZ
      refine ⟨1, one_ne_zero, fun x hx i j => ⟨⟨x i j, ?_⟩, by simp⟩⟩
      have : x i j = d⁻¹ * (d * x i j) := by rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      rw [this]
      exact mul_mem hdinv (hbd x hx i j)
  have hsmulR : ∀ r : R, ∀ x ∈ O, r • x ∈ O := fun r x hx => by
    have : r • x = (r : v.adicCompletion ℚ) • x := rfl
    rw [this]
    exact hsmul r r.2 x hx
  obtain ⟨h, hU, H⟩ := exists_isUnit_conj_integral (R := R) O hsmulR dR hdR hbddR
  refine ⟨hU.unit, fun x hx i j => ?_⟩
  obtain ⟨r, hr⟩ := H x hx i j
  rw [Matrix.coe_units_inv, IsUnit.unit_spec, ← hr]
  exact r.2

end Local

end Ws50W2a

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (O : Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hsmul : ∀ r : v.adicCompletion ℚ, r ∈ v.adicCompletionIntegers ℚ → ∀ x ∈ O, r • x ∈ O)
    (hbdd : ∃ d : v.adicCompletion ℚ, d ≠ 0 ∧ ∀ x ∈ O, ∀ i j, d * x i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ h : GL (Fin 2) (v.adicCompletion ℚ), ∀ x ∈ O, ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * x *
        (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ := by
  exact Ws50W2a.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring v O hsmul hbdd

end S_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring
end P2MW
export P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring (solution)
