-- Prove2me | solution 1 for LiouvilleDiffAlg.liouvilleForm_descent_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:12:21.982059+00:00
-- url     : https://prove2.me/submissions/44e59800-1eca-4b04-bb95-e2cffb620206

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form

open scoped Differential
open LiouvilleDiffAlg

set_option warn.classDefReducibility false

private noncomputable def subDiff {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) : Differential K :=
  ⟨Derivation.mk'
    { toFun := fun x => ⟨(x : G)′, hK x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by simp) }
    (fun a b => Subtype.ext (by simp [Derivation.leibniz]))⟩

private lemma subDiff_coe {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) (x : K) :
    (((subDiff K hK).deriv x : K) : G) = (x : G)′ := rfl

private lemma subDiff_alg {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) :
    @DifferentialAlgebra K G _ _ _ (subDiff K hK) _ :=
  @DifferentialAlgebra.mk K G _ _ _ (subDiff K hK) _ (fun _ => rfl)

theorem solution {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    (hconst : constants G ⊆ (K : Set G)) {t : G} (ht : IsAlgebraic K t) {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h := by
  classical
  letI : Differential K := subDiff K hK
  haveI : DifferentialAlgebra K G := subDiff_alg K hK
  haveI : CharZero K := RingHom.charZero (algebraMap K G)
  let M : IntermediateField K G := IntermediateField.adjoin K {t}
  haveI : FiniteDimensional K M := IntermediateField.adjoin.finiteDimensional ht.isIntegral
  have hLiou : IsLiouville K M := inferInstance
  -- the derivation of `M` is the restriction of the one of `G`
  have hcompat : ∀ x : M, ((x′ : M) : G) = (x : G)′ := fun x =>
    Differential.algHom_deriv' M.val (Subtype.val_injective) x
  have hLM : ∀ x ∈ IntermediateField.adjoin F (insert t (K : Set G)), x ∈ M := by
    have : IntermediateField.adjoin F (insert t (K : Set G)) ≤ M.restrictScalars F := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with rfl | hx
      · exact IntermediateField.subset_adjoin K _ rfl
      · exact IntermediateField.algebraMap_mem M ⟨x, hx⟩
    exact fun x hx => this hx
  obtain ⟨n, c, u, v, hc, hu, hv, hfe⟩ := hL
  let cK : Fin n → K := fun i => ⟨c i, hconst (hc i)⟩
  let uM : Fin n → M := fun i => ⟨u i, hLM _ (hu i).1⟩
  let vM : M := ⟨v, hLM _ hv⟩
  let a : K := ⟨h, hh⟩
  have hcK : ∀ i, (cK i)′ = 0 := fun i => Subtype.ext (hc i)
  have hlog : ∀ x : M, (((Differential.logDeriv x : M)) : G) = (x : G)′ / (x : G) := by
    intro x
    rw [Differential.logDeriv]
    push_cast
    rw [hcompat]
  have key := hLiou.isLiouville a (Fin n) cK hcK uM vM (by
    apply Subtype.val_injective
    push_cast
    rw [hcompat vM]
    have : ∀ x, (((Differential.logDeriv (uM x) : M)) : G) = (u x)′ / u x := fun x => hlog _
    simp only [this]
    exact hfe)
  obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, hfin⟩ := key
  have hcoe : ∀ x : K, (((x′ : K)) : G) = (x : G)′ := fun x => rfl
  have hG : h = ∑ x, (c₀ x : G) * ((u₀ x : G)′ / (u₀ x : G)) + (v₀ : G)′ := by
    have := congrArg (fun y : K => (y : G)) hfin
    simpa [Differential.logDeriv, hcoe] using this
  let s : Finset ι₀ := Finset.univ.filter (fun x => u₀ x ≠ 0)
  have hsum : ∑ x, (c₀ x : G) * ((u₀ x : G)′ / (u₀ x : G)) =
      ∑ x ∈ s, (c₀ x : G) * ((u₀ x : G)′ / (u₀ x : G)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : u₀ x = 0
    · simp [hx]
    · simp [hx]
  let e := s.equivFin
  refine ⟨s.card, fun i => (c₀ (e.symm i).1 : G), fun i => (u₀ (e.symm i).1 : G), (v₀ : G),
    ?_, ?_, v₀.2, ?_⟩
  · intro i
    exact congrArg (fun y : K => (y : G)) (hc₀ (e.symm i).1)
  · intro i
    refine ⟨(u₀ _).2, fun h0 => ?_⟩
    exact (Finset.mem_filter.1 (e.symm i).2).2 (Subtype.ext h0)
  · rw [hG, hsum, ← Finset.sum_coe_sort s]
    congr 1
    exact (Equiv.sum_comp e.symm
      (fun x : s => (c₀ x.1 : G) * ((u₀ x.1 : G)′ / (u₀ x.1 : G)))).symm
