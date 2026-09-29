-- Prove2me | solution 1 for ModularCurve.CharPModel.relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a2b57cf6-60c6-514c-b014-5a822b668b9a

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Relrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField

namespace RelfinrankTransfer

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private abbrev bKj : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

private abbrev bTop : IntermediateField (bKj K) (LaurentSeries K) :=
  IntermediateField.adjoin (bKj K) ({jqNModC K N} : Set (LaurentSeries K))

private abbrev bFC : IntermediateField K (LaurentSeries K) := modularFunctionFieldC K N

private theorem jq_mem_bKj : jqModC K ∈ bKj K := subset_adjoin K _ (Set.mem_singleton _)

private abbrev bjg : bKj K := ⟨jqModC K, jq_mem_bKj K⟩

variable {K N} in
private theorem jqNModC_congr' {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    jqNModC K m = jqNModC K n := by
  subst h; rfl

private theorem bTop_restrictScalars : (bTop K N).restrictScalars K = bFC K N := by
  have h := adjoin_adjoin_left K ({jqModC K} : Set (LaurentSeries K))
    ({jqNModC K N} : Set (LaurentSeries K))
  rw [Set.singleton_union] at h
  exact h

variable {K N} in
private theorem mem_bTop_of_mem_bFC {x : LaurentSeries K} (hx : x ∈ bFC K N) : x ∈ bTop K N :=
  (mem_restrictScalars K).mp ((bTop_restrictScalars K N).symm ▸ hx)

private theorem one_le_dedekindPsi'' : 1 ≤ dedekindPsi N := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  refine hN.trans ?_
  unfold dedekindPsi
  have hmem : 1 ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) hmem
  simpa using this

variable (hdeg : Module.finrank (bKj K) (bTop K N) = dedekindPsi N)

include hdeg in
private theorem finiteDimensional_bTop : FiniteDimensional (bKj K) (bTop K N) :=
  Module.finite_of_finrank_pos (by rw [hdeg]; exact one_le_dedekindPsi'' N)

include hdeg in
private theorem isIntegral_jN : IsIntegral (bKj K) (jqNModC K N) := by
  haveI := finiteDimensional_bTop K N hdeg
  have h : IsIntegral (bKj K) (AdjoinSimple.gen (bKj K) (jqNModC K N)) :=
    IsIntegral.of_finite (bKj K) _
  exact isIntegral_iff.mp h

include hdeg in
private theorem natDegree_minpoly' :
    (minpoly (bKj K) (jqNModC K N)).natDegree = dedekindPsi N := by
  rw [← adjoin.finrank (isIntegral_jN K N hdeg), hdeg]

private theorem qExpand_algebraMap' (c : K) :
    qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c := by
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private def qExpandK' : LaurentSeries K →ₐ[K] LaurentSeries K :=
  { qExpand K N with commutes' := qExpand_algebraMap' K N }

private def bbase : bKj K →ₐ[K] LaurentSeries K := (qExpandK' K N).comp (bKj K).val

private theorem bbase_apply (x : bKj K) : bbase K N x = qExpand K N (x : LaurentSeries K) := rfl

private theorem bbase_jg : bbase K N (bjg K) = jqNModC K N := rfl

variable (data : ModularPolynomialData N)

private def evalAtJK' : Polynomial ℤ →+* bKj K := (Polynomial.aeval (R := ℤ) (bjg K)).toRingHom

private def bQK : Polynomial (bKj K) := data.Φ.map (evalAtJK' K)

private theorem bQK_monic : (bQK K N data).Monic := data.monic.map _

private theorem bQK_natDegree : (bQK K N data).natDegree = dedekindPsi N := by
  rw [bQK, data.monic.natDegree_map, data.natDegree_eq]

private theorem algebraMap_comp_evalAtJK' :
    (algebraMap (bKj K) (LaurentSeries K)).comp (evalAtJK' K)
      = (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJK']

private theorem bbase_comp_evalAtJK' :
    (bbase K N).toRingHom.comp (evalAtJK' K)
      = (Polynomial.aeval (R := ℤ) (jqNModC K N)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.comp_apply, evalAtJK', AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Polynomial.aeval_X]
  exact bbase_jg K N

private theorem brel :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom (jqNModC K N) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero K 1
  rwa [jqNModC_one, jqNModC_congr' (Nat.one_mul N)] at h

private theorem brel_symm (hsymm : EvalSymm data.Φ) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC K N)).toRingHom (jqModC K) = 0 := by
  have h := data.eval_jqNModC_of_mul_eq_zero hsymm K 1
  rwa [jqNModC_one, jqNModC_congr' (Nat.one_mul N)] at h

private theorem bQK_aeval_jN : Polynomial.aeval (jqNModC K N) (bQK K N data) = 0 := by
  rw [Polynomial.aeval_def, bQK, Polynomial.eval₂_map, algebraMap_comp_evalAtJK']
  exact brel K N data

include hdeg in
private theorem minpoly_eq_bQK : minpoly (bKj K) (jqNModC K N) = bQK K N data := by
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (isIntegral_jN K N hdeg))
    (bQK_monic K N data) (minpoly.dvd _ _ (bQK_aeval_jN K N data)) ?_
  rw [bQK_natDegree, natDegree_minpoly' K N hdeg]

include hdeg in

private theorem minpoly_eval₂_bbase (hsymm : EvalSymm data.Φ) :
    (minpoly (bKj K) (jqNModC K N)).eval₂ (bbase K N).toRingHom (jqModC K) = 0 := by
  rw [minpoly_eq_bQK K N hdeg data, bQK, Polynomial.eval₂_map, bbase_comp_evalAtJK']
  exact brel_symm K N data hsymm

variable (hsymm : EvalSymm data.Φ)

private def bliftHom : bTop K N →+* LaurentSeries K :=
  (AdjoinRoot.lift (bbase K N).toRingHom (jqModC K) (minpoly_eval₂_bbase K N hdeg data hsymm)).comp
    (adjoinRootEquivAdjoin (bKj K) (isIntegral_jN K N hdeg)).symm.toAlgHom.toRingHom

private theorem bliftHom_gen :
    bliftHom K N hdeg data hsymm (AdjoinSimple.gen (bKj K) (jqNModC K N)) = jqModC K := by
  rw [bliftHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin (bKj K) (isIntegral_jN K N hdeg)).symm.toAlgHom.toRingHom
        (AdjoinSimple.gen (bKj K) (jqNModC K N))
      = AdjoinRoot.root (minpoly (bKj K) (jqNModC K N)) from
    adjoinRootEquivAdjoin_symm_apply_gen (bKj K) (isIntegral_jN K N hdeg)]
  exact AdjoinRoot.lift_root _

private theorem bliftHom_algebraMap (c : bKj K) :
    bliftHom K N hdeg data hsymm (algebraMap (bKj K) (bTop K N) c) = bbase K N c := by
  rw [bliftHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin (bKj K) (isIntegral_jN K N hdeg)).symm.toAlgHom.toRingHom
        (algebraMap (bKj K) (bTop K N) c)
      = algebraMap (bKj K) (AdjoinRoot (minpoly (bKj K) (jqNModC K N))) c from
    (adjoinRootEquivAdjoin (bKj K) (isIntegral_jN K N hdeg)).symm.commutes c]
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

private def btoTop : bFC K N →+* bTop K N where
  toFun x := ⟨(x : LaurentSeries K), mem_bTop_of_mem_bFC x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def bsigmaHom : bFC K N →+* LaurentSeries K :=
  (bliftHom K N hdeg data hsymm).comp (btoTop K N)

private theorem bsigmaHom_jq :
    bsigmaHom K N hdeg data hsymm ⟨jqModC K, jqModC_mem K N⟩ = jqNModC K N := by
  show bliftHom K N hdeg data hsymm (btoTop K N ⟨jqModC K, jqModC_mem K N⟩) = _
  rw [show btoTop K N ⟨jqModC K, jqModC_mem K N⟩ = algebraMap (bKj K) (bTop K N) (bjg K) from
    Subtype.ext rfl, bliftHom_algebraMap, bbase_jg]

private theorem bsigmaHom_jN :
    bsigmaHom K N hdeg data hsymm ⟨jqNModC K N, jqNModC_mem K N⟩ = jqModC K := by
  show bliftHom K N hdeg data hsymm (btoTop K N ⟨jqNModC K N, jqNModC_mem K N⟩) = _
  rw [show btoTop K N ⟨jqNModC K N, jqNModC_mem K N⟩ = AdjoinSimple.gen (bKj K) (jqNModC K N) from
    Subtype.ext rfl]
  exact bliftHom_gen K N hdeg data hsymm

private theorem bsigmaHom_algebraMap (c : K) :
    bsigmaHom K N hdeg data hsymm (algebraMap K (bFC K N) c) = algebraMap K (LaurentSeries K) c := by
  show bliftHom K N hdeg data hsymm (btoTop K N (algebraMap K (bFC K N) c)) = _
  rw [show btoTop K N (algebraMap K (bFC K N) c)
      = algebraMap (bKj K) (bTop K N) (algebraMap K (bKj K) c) from Subtype.ext rfl,
    bliftHom_algebraMap]
  exact (bbase K N).commutes c

private theorem bsigmaHom_mem (x : bFC K N) : bsigmaHom K N hdeg data hsymm x ∈ bFC K N := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rcases hy with rfl | hy
      · rw [bsigmaHom_jq]; exact jqNModC_mem K N
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [bsigmaHom_jN]; exact jqModC_mem K N
  | algebraMap c =>
      have e : (⟨algebraMap K (LaurentSeries K) c, (bFC K N).algebraMap_mem c⟩ : bFC K N)
          = algebraMap K (bFC K N) c := rfl
      rw [e, bsigmaHom_algebraMap]
      exact (bFC K N).algebraMap_mem c
  | add y z hy hz ihy ihz =>
      have e : (⟨y + z, add_mem hy hz⟩ : bFC K N) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, map_add]; exact add_mem ihy ihz
  | inv y hy ih =>
      have e : (⟨y⁻¹, inv_mem hy⟩ : bFC K N) = (⟨y, hy⟩ : bFC K N)⁻¹ := rfl
      rw [e, map_inv₀]; exact inv_mem ih
  | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, mul_mem hy hz⟩ : bFC K N) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, map_mul]; exact mul_mem ihy ihz

private def bendo : bFC K N →ₐ[K] bFC K N where
  toFun x := ⟨bsigmaHom K N hdeg data hsymm x, bsigmaHom_mem K N hdeg data hsymm x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext (bsigmaHom_algebraMap K N hdeg data hsymm c)

private theorem bendo_jq :
    bendo K N hdeg data hsymm ⟨jqModC K, jqModC_mem K N⟩ = ⟨jqNModC K N, jqNModC_mem K N⟩ :=
  Subtype.ext (bsigmaHom_jq K N hdeg data hsymm)

private theorem bendo_jN :
    bendo K N hdeg data hsymm ⟨jqNModC K N, jqNModC_mem K N⟩ = ⟨jqModC K, jqModC_mem K N⟩ :=
  Subtype.ext (bsigmaHom_jN K N hdeg data hsymm)

private theorem balgHom_ext {f g : bFC K N →ₐ[K] bFC K N}
    (h1 : f ⟨jqModC K, jqModC_mem K N⟩ = g ⟨jqModC K, jqModC_mem K N⟩)
    (h2 : f ⟨jqNModC K N, jqNModC_mem K N⟩ = g ⟨jqNModC K N, jqNModC_mem K N⟩) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := bFC K N)
    (s := ({jqModC K, jqNModC K N} : Set (LaurentSeries K))) rfl (fun x hx => ?_)
  rcases hx with rfl | hx
  · exact h1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h2

private theorem bendo_comp_bendo :
    (bendo K N hdeg data hsymm).comp (bendo K N hdeg data hsymm) = AlgHom.id K (bFC K N) := by
  refine balgHom_ext K N ?_ ?_
  · rw [AlgHom.comp_apply, bendo_jq, bendo_jN]; rfl
  · rw [AlgHom.comp_apply, bendo_jN, bendo_jq]; rfl

private def bsigma : bFC K N ≃ₐ[K] bFC K N :=
  AlgEquiv.ofAlgHom (bendo K N hdeg data hsymm) (bendo K N hdeg data hsymm)
    (bendo_comp_bendo K N hdeg data hsymm) (bendo_comp_bendo K N hdeg data hsymm)

private theorem bsigma_jq :
    bsigma K N hdeg data hsymm ⟨jqModC K, jqModC_mem K N⟩ = ⟨jqNModC K N, jqNModC_mem K N⟩ :=
  bendo_jq K N hdeg data hsymm

private theorem relfinrank_map_map'' {E E' : Type*} [Field E] [Field E'] [Algebra K E]
    [Algebra K E'] (A B : IntermediateField K E) (f : E →ₐ[K] E') :
    IntermediateField.relfinrank (A.map f) (B.map f) = IntermediateField.relfinrank A B := by
  show Subfield.relfinrank (A.map f).toSubfield (B.map f).toSubfield
    = Subfield.relfinrank A.toSubfield B.toSubfield
  have hA : (A.map f).toSubfield = A.toSubfield.map (f : E →+* E') :=
    SetLike.ext' (by rw [coe_toSubfield, coe_map, Subfield.coe_map, coe_toSubfield]; rfl)
  have hB : (B.map f).toSubfield = B.toSubfield.map (f : E →+* E') :=
    SetLike.ext' (by rw [coe_toSubfield, coe_map, Subfield.coe_map, coe_toSubfield]; rfl)
  rw [hA, hB]
  exact Subfield.relfinrank_map_map _ _ _

private theorem relfinrank_lift_lift' {E : Type*} [Field E] [Algebra K E]
    (F : IntermediateField K E) (A B : IntermediateField K F) :
    IntermediateField.relfinrank (lift A) (lift B) = IntermediateField.relfinrank A B :=
  relfinrank_map_map'' K A B F.val

include hdeg data hsymm in

private theorem relfinrank_jN_eq_relfinrank_j :
    (IntermediateField.adjoin K ({jqNModC K N} : Set (LaurentSeries K))).relfinrank (bFC K N)
      = (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank (bFC K N) := by

  have e1 : lift (adjoin K ({⟨jqNModC K N, jqNModC_mem K N⟩} : Set (bFC K N)))
      = IntermediateField.adjoin K ({jqNModC K N} : Set (LaurentSeries K)) := by
    rw [lift_adjoin, Set.image_singleton]
  have e2 : lift (adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (bFC K N)))
      = IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
    rw [lift_adjoin, Set.image_singleton]
  have h1 := relfinrank_lift_lift' K (bFC K N)
    (adjoin K ({⟨jqNModC K N, jqNModC_mem K N⟩} : Set (bFC K N))) ⊤
  rw [e1, lift_top] at h1
  have h2 := relfinrank_lift_lift' K (bFC K N)
    (adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (bFC K N))) ⊤
  rw [e2, lift_top] at h2
  rw [h1, h2]

  have e4 : (adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (bFC K N))).map
      (bsigma K N hdeg data hsymm).toAlgHom
        = adjoin K ({⟨jqNModC K N, jqNModC_mem K N⟩} : Set (bFC K N)) := by
    rw [adjoin_map, Set.image_singleton]
    show adjoin K {bsigma K N hdeg data hsymm ⟨jqModC K, jqModC_mem K N⟩} = _
    rw [bsigma_jq]
  have e5 : (⊤ : IntermediateField K (bFC K N)).map (bsigma K N hdeg data hsymm).toAlgHom = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact ⟨(bsigma K N hdeg data hsymm).symm x, trivial,
      (bsigma K N hdeg data hsymm).apply_symm_apply x⟩
  have h3 := relfinrank_map_map'' K (adjoin K ({⟨jqModC K, jqModC_mem K N⟩} : Set (bFC K N))) ⊤
    (bsigma K N hdeg data hsymm).toAlgHom
  rw [e4, e5] at h3
  exact h3

end RelfinrankTransfer

end

open ModularCurve in
theorem solution
    (N : ℕ) [NeZero N] (k : Type*) [Field k]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N) :
    (IntermediateField.adjoin k {(jqNModC k N : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N := by

  have hle : IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))
      ≤ modularFunctionFieldC k N :=
    IntermediateField.adjoin.mono k _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have e : IntermediateField.extendScalars hle
      = IntermediateField.adjoin (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))
          ({jqNModC k N} : Set (LaurentSeries k)) :=
    IntermediateField.restrictScalars_injective k (by
      rw [RelfinrankTransfer.bTop_restrictScalars]
      rfl)
  have hdeg' : Module.finrank (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))
      (IntermediateField.adjoin (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))
        ({jqNModC k N} : Set (LaurentSeries k))) = dedekindPsi N := by
    rw [← e, ← IntermediateField.relfinrank_eq_finrank_of_le hle]
    exact hdeg
  rw [RelfinrankTransfer.relfinrank_jN_eq_relfinrank_j k N hdeg' data hsym]
  exact hdeg

end S_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm
end P2MW
export P2MW.S_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm (solution)
