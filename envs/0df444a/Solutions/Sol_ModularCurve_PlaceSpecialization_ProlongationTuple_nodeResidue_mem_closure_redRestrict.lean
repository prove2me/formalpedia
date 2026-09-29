-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_mem_closure_redRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/568657df-2ce9-511f-b5bf-6bd97dd01ef9

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDescentTower
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver
import Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_mem_closure_redRestrict
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace SatL0

theorem mem_modularFunctionFieldC_of_coeffMap_mem {k₀ k : Type*} [Field k₀] [Field k] (σ : k₀ →+* k)
    (N : ℕ) [NeZero N] (h : LaurentSeries k₀) (hmem : coeffMap σ h ∈ modularFunctionFieldC k N) :
    h ∈ modularFunctionFieldC k₀ N := by
  classical
  by_cases hh : h = 0
  · rw [hh]; exact zero_mem _

  have hsmul : ∀ (c : k₀) (x : LaurentSeries k₀), coeffMap σ (c • x) = σ c • coeffMap σ x := by
    intro c x
    ext m
    simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]
  have hC : ∀ c : k₀, HahnSeries.C c ∈ modularFunctionFieldC k₀ N := fun c => by
    have hc := (modularFunctionFieldC k₀ N).algebraMap_mem c
    rwa [LaurentSeries.algebraMap_apply] at hc

  have hspanL : ∀ S : Set (LaurentSeries k₀), (∀ y ∈ S, y ∈ modularFunctionFieldC k₀ N) →
      ∀ y ∈ Submodule.span k₀ S, y ∈ modularFunctionFieldC k₀ N := by
    intro S hS y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS z hz
    | zero => exact zero_mem _
    | add z w _ _ hz hw => exact add_mem hz hw
    | smul c z _ hz => rw [← HahnSeries.C_mul_eq_smul]; exact mul_mem (hC c) hz

  have hspan_mul :
      ∀ x ∈ Submodule.span k (coeffMap σ '' (modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))),
      ∀ y ∈ Submodule.span k (coeffMap σ '' (modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))),
        x * y ∈ Submodule.span k (coeffMap σ '' (modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxS =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hyS =>
        obtain ⟨a, ha, rfl⟩ := hxS
        obtain ⟨b, hb, rfl⟩ := hyS
        exact Submodule.subset_span ⟨a * b, mul_mem ha hb, map_mul _ _ _⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul c y _ hy =>
        rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
        exact Submodule.smul_mem _ c hy
    | zero => intro y _; rw [zero_mul]; exact zero_mem _
    | add x z _ _ hx hz => intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
    | smul c x _ hx =>
      intro y hy
      rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ c (hx y hy)

  have hsub : ∀ x ∈ Algebra.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k)),
      x ∈ Submodule.span k (coeffMap σ '' (modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Submodule.subset_span ⟨jqModC k₀, jqModC_mem k₀ N, coeffMap_jqModC σ⟩
      · exact Submodule.subset_span ⟨jqNModC k₀ N, jqNModC_mem k₀ N, coeffMap_jqNModC σ N⟩
    | algebraMap r =>
      rw [LaurentSeries.algebraMap_apply, ← mul_one (HahnSeries.C r), HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨1, one_mem _, map_one _⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact hspan_mul x hx y hy

  have hrep : ∀ x ∈ Submodule.span k (coeffMap σ '' (modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))),
      ∃ (n : ℕ) (t : Fin n → LaurentSeries k₀) (c : Fin n → k),
        (∀ i, t i ∈ modularFunctionFieldC k₀ N) ∧ LinearIndependent k₀ t ∧
          x = ∑ i, c i • coeffMap σ (t i) := by
    intro x hx
    rw [Set.image_eq_range, Finsupp.mem_span_range_iff_exists_finsupp] at hx
    obtain ⟨cx, hcx⟩ := hx

    set T : Set (LaurentSeries k₀) :=
      (fun l : ↥(modularFunctionFieldC k₀ N : Set (LaurentSeries k₀)) => (l : LaurentSeries k₀)) ''
        (cx.support : Set ↥(modularFunctionFieldC k₀ N : Set (LaurentSeries k₀))) with hT
    have hTfin : T.Finite := (Finset.finite_toSet _).image _
    haveI := FiniteDimensional.span_of_finite k₀ hTfin
    let B := Module.finBasis k₀ ↥(Submodule.span k₀ T)
    have hTL : ∀ y ∈ T, y ∈ modularFunctionFieldC k₀ N := by
      rintro _ ⟨l, -, rfl⟩
      exact l.2
    have htL : ∀ i, (B i : LaurentSeries k₀) ∈ modularFunctionFieldC k₀ N :=
      fun i => hspanL _ hTL _ (B i).2
    have htind : LinearIndependent k₀ fun i => (B i : LaurentSeries k₀) :=
      B.linearIndependent.map' (Submodule.span k₀ T).subtype (Submodule.ker_subtype _)

    have hWspan : ∀ y ∈ Submodule.span k₀ T, coeffMap σ y
        ∈ Submodule.span k (Set.range fun i => coeffMap σ (B i : LaurentSeries k₀)) := by
      intro y hy
      have hy' : y ∈ Submodule.span k₀ (Set.range fun i => (B i : LaurentSeries k₀)) := by
        have hrange : Set.range (fun i => (B i : LaurentSeries k₀))
            = (Submodule.span k₀ T).subtype '' Set.range B :=
          Set.range_comp (Submodule.span k₀ T).subtype B
        rw [hrange, Submodule.span_image, B.span_eq, Submodule.map_subtype_top]
        exact hy
      clear hy
      induction hy' using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
      | smul a z _ hz => rw [hsmul]; exact Submodule.smul_mem _ _ hz
    have hxspan : x ∈ Submodule.span k (Set.range fun i => coeffMap σ (B i : LaurentSeries k₀)) := by
      rw [← hcx, Finsupp.sum]
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (hWspan _ ?_)
      exact Submodule.subset_span ⟨l, Finset.mem_coe.mpr hl, rfl⟩
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxspan
    refine ⟨Module.finrank k₀ ↥(Submodule.span k₀ T), fun i => (B i : LaurentSeries k₀), fun i => c i, htL,
      htind, ?_⟩
    rw [← hc, Finsupp.sum_fintype _ _ (fun i => by exact zero_smul k _)]

  have hmem' : coeffMap σ h ∈ IntermediateField.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k)) :=
    hmem
  obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.mp hmem'
  obtain ⟨n₁, a, c, haL, haind, hs_eq⟩ := hrep s (hsub s hs)
  obtain ⟨n₂, b, d, hbL, hbind, hr_eq⟩ := hrep r (hsub r hr)
  have hinj : ∀ y : LaurentSeries k₀, coeffMap σ y = 0 → y = 0 := by
    intro y hy
    ext m
    have hm := congrArg (fun z : LaurentSeries k => z.coeff m) hy
    simp only [coeffMap_coeff] at hm
    simpa using hm
  have hs0 : s ≠ 0 := by
    intro h0
    apply hh
    apply hinj
    rw [hrs, h0, div_zero]
  have hrel : s * coeffMap σ h = r := by
    rw [hrs]
    field_simp

  have hahind : LinearIndependent k₀ fun i => a i * h := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : (∑ i, g i • a i) * h = ∑ i, g i • (a i * h) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]
    rw [hg] at hsum
    have hzero : ∑ i, g i • a i = 0 := (mul_eq_zero.mp hsum).resolve_right hh
    exact Fintype.linearIndependent_iff.mp haind g hzero i

  have hdep : ¬ LinearIndependent k₀ (Sum.elim (fun i => a i * h) b) := by
    intro hF
    have hF' : LinearIndependent k₀ (Sum.elim (fun i => a i * h) b ∘ finSumFinEquiv.symm) :=
      (linearIndependent_equiv finSumFinEquiv.symm).mpr hF
    have hG' := linearIndependent_coeffMap σ hF'
    have hG : LinearIndependent k fun x => coeffMap σ (Sum.elim (fun i => a i * h) b x) :=
      (linearIndependent_equiv finSumFinEquiv.symm
        (f := fun x => coeffMap σ (Sum.elim (fun i => a i * h) b x))).mp hG'
    have hdis := (linearIndependent_sum.mp hG).2.2
    have hr1 : r ∈ Submodule.span k
        (Set.range ((fun x => coeffMap σ (Sum.elim (fun i => a i * h) b x)) ∘ Sum.inl)) := by
      rw [← hrel, hs_eq, Finset.sum_mul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← HahnSeries.C_mul_eq_smul, mul_assoc, ← map_mul, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hr2 : r ∈ Submodule.span k
        (Set.range ((fun x => coeffMap σ (Sum.elim (fun i => a i * h) b x)) ∘ Sum.inr)) := by
      rw [hr_eq]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hr0 : r = 0 := (Submodule.disjoint_def.mp hdis) r hr1 hr2
    apply hh
    apply hinj
    have h0 : s * coeffMap σ h = 0 := by rw [hrel, hr0]
    exact (mul_eq_zero.mp h0).resolve_left hs0

  have hndis : ¬ Disjoint (Submodule.span k₀ (Set.range fun i => a i * h)) (Submodule.span k₀ (Set.range b)) := by
    intro hdis
    exact hdep (linearIndependent_sum.mpr ⟨hahind, hbind, hdis⟩)
  rw [Submodule.disjoint_def] at hndis
  simp only [not_forall, exists_prop] at hndis
  obtain ⟨x, hx1, hx2, hx0⟩ := hndis

  have hwx : ∀ y ∈ Submodule.span k₀ (Set.range fun i => a i * h),
      ∃ w ∈ modularFunctionFieldC k₀ N, w * h = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨a i, haL i, rfl⟩
    | zero => exact ⟨0, zero_mem _, zero_mul _⟩
    | add z w _ _ hz hw =>
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨u + v, add_mem hu hv, add_mul _ _ _⟩
    | smul g z _ hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      refine ⟨g • u, ?_, ?_⟩
      · rw [← HahnSeries.C_mul_eq_smul]; exact mul_mem (hC g) hu
      · rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]
  obtain ⟨w, hwL, rfl⟩ := hwx x hx1
  have hxL : w * h ∈ modularFunctionFieldC k₀ N :=
    hspanL _ (by rintro _ ⟨j, rfl⟩; exact hbL j) _ hx2
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hx0 (zero_mul _)
  rw [← inv_mul_cancel_left₀ hw0 h]
  exact mul_mem (inv_mem hwL) hxL

theorem mem_closure_of_arithFrobC_pow_smul_eq
    {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [PerfectField k] {N : ℕ} [NeZero N]
    (d : ℕ) (x : ↥(modularFunctionFieldC k N)) (hx : (arithFrobC q k N) ^ d • x = x) :
    x ∈ Subfield.closure (Set.range (fun c : {c : k // c ^ (q ^ d) = c} => algebraMap k ↥(modularFunctionFieldC k N) c.1) ∪ {(⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)), (⟨jqNModC k N, jqNModC_mem k N⟩ : ↥(modularFunctionFieldC k N))}) := by
  classical

  let kd : Subfield k :=
    { carrier := {c : k | c ^ (q ^ d) = c}
      mul_mem' := fun {a b} (ha : a ^ (q ^ d) = a) (hb : b ^ (q ^ d) = b) => by
        show (a * b) ^ (q ^ d) = a * b; rw [mul_pow, ha, hb]
      one_mem' := by show (1 : k) ^ (q ^ d) = 1; exact one_pow _
      add_mem' := fun {a b} (ha : a ^ (q ^ d) = a) (hb : b ^ (q ^ d) = b) => by
        show (a + b) ^ (q ^ d) = a + b; rw [add_pow_char_pow, ha, hb]
      zero_mem' := by
        show (0 : k) ^ (q ^ d) = 0; exact zero_pow (pow_ne_zero d (Fact.out : q.Prime).ne_zero)
      neg_mem' := fun {a} (ha : a ^ (q ^ d) = a) => by
        show (-a) ^ (q ^ d) = -a; rw [← iterateFrobenius_def, map_neg, iterateFrobenius_def, ha]
      inv_mem' := fun a (ha : a ^ (q ^ d) = a) => by
        show (a⁻¹) ^ (q ^ d) = a⁻¹; rw [inv_pow, ha] }
  have hkd : ∀ c : k, c ∈ kd ↔ c ^ (q ^ d) = c := fun c => Iff.rfl

  have hcoe : ∀ (m : ℕ) (y : ↥(modularFunctionFieldC k N)) (n : ℤ),
      (((coeffSemilinearAut N (frobeniusEquiv k q)) ^ m • y : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n
        = ((y : LaurentSeries k).coeff n) ^ (q ^ m) := by
    intro m
    induction m with
    | zero => intro y n; rw [pow_zero, one_smul, pow_zero, pow_one]
    | succ m ih =>
        intro y n
        rw [pow_succ', mul_smul, coe_coeffSemilinearAut_smul, coeffMap_coeff, ih, pow_succ, pow_mul]
        rfl
  have hfix : ∀ n : ℤ, ((x : LaurentSeries k).coeff n) ^ (q ^ d) = (x : LaurentSeries k).coeff n := by
    intro n
    have h1 : (((arithFrobC q k N) ^ d • x : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n = (x : LaurentSeries k).coeff n := by
      rw [hx]
    rw [show arithFrobC q k N = coeffSemilinearAut N (frobeniusEquiv k q) from rfl, hcoe] at h1
    exact h1

  have hseries : ∃ h : LaurentSeries ↥kd, coeffMap kd.subtype h = (x : LaurentSeries k) := by
    refine ⟨⟨fun n => ⟨(x : LaurentSeries k).coeff n, (hkd _).mpr (hfix n)⟩, ?_⟩, ?_⟩
    · have hsupp : (Function.support fun n => (⟨(x : LaurentSeries k).coeff n, (hkd _).mpr (hfix n)⟩ : ↥kd))
          = Function.support (x : LaurentSeries k).coeff := by
        ext n; simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
      rw [hsupp]; exact (x : LaurentSeries k).isPWO_support'
    · ext n; rfl
  obtain ⟨h, hh⟩ := hseries

  have hmem : h ∈ modularFunctionFieldC (↥kd) N :=
    mem_modularFunctionFieldC_of_coeffMap_mem kd.subtype N h (hh ▸ x.2)

  set S : Subfield ↥(modularFunctionFieldC k N) :=
    Subfield.closure (Set.range (fun c : {c : k // c ^ (q ^ d) = c} => algebraMap k ↥(modularFunctionFieldC k N) c.1) ∪ {(⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)), (⟨jqNModC k N, jqNModC_mem k N⟩ : ↥(modularFunctionFieldC k N))}) with hS

  let val : ↥(modularFunctionFieldC k N) →+* LaurentSeries k := (modularFunctionFieldC k N).toSubfield.subtype
  have hval : ∀ z : ↥(modularFunctionFieldC k N), val z = (z : LaurentSeries k) := fun z => rfl
  suffices hsuff : coeffMap kd.subtype h ∈ S.map val by
    rw [hh] at hsuff
    obtain ⟨y, hyS, hy⟩ := Subfield.mem_map.mp hsuff
    have : y = x := Subtype.ext (by rw [← hval]; exact hy)
    exact this ▸ hyS
  clear hh
  change h ∈ Subfield.closure (Set.range (algebraMap ↥kd (LaurentSeries ↥kd)) ∪ {jqModC ↥kd, jqNModC ↥kd N}) at hmem
  induction hmem using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | rfl | rfl
      · refine Subfield.mem_map.mpr ⟨algebraMap k ↥(modularFunctionFieldC k N) (c : k), ?_, ?_⟩
        · exact Subfield.subset_closure (Or.inl ⟨⟨(c : k), c.2⟩, rfl⟩)
        · rw [hval]
          show algebraMap k (LaurentSeries k) (c : k) = coeffMap kd.subtype (algebraMap (↥kd) (LaurentSeries ↥kd) c)
          rw [LaurentSeries.algebraMap_apply, LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.C_apply,
            coeffMap_single]
          rfl
      · refine Subfield.mem_map.mpr ⟨⟨jqModC k, jqModC_mem k N⟩, Subfield.subset_closure (Or.inr (Set.mem_insert _ _)), ?_⟩
        rw [hval, coeffMap_jqModC]
      · refine Subfield.mem_map.mpr ⟨⟨jqNModC k N, jqNModC_mem k N⟩, Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl)), ?_⟩
        rw [hval, coeffMap_jqNModC]
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem mem_range_redRestrict_of_pow_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card (Set.range (NodeLocalized.redRestrict red K)) = q ^ d)
    (c : k) (hc : c ^ (q ^ d) = c) : c ∈ Set.range (NodeLocalized.redRestrict red K) := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hqd : 0 < q ^ d := pow_pos (Fact.out : q.Prime).pos d

  set Rg : Subring k := (NodeLocalized.redRestrict red K).range with hRg
  have hRgS : (Rg : Set k) = Set.range (NodeLocalized.redRestrict red K) := RingHom.coe_range _
  have hcardRg : Nat.card ↥Rg = q ^ d := by
    rw [← hcard, ← hRgS]; rfl
  haveI : Finite ↥Rg := Nat.finite_of_card_ne_zero (by rw [hcardRg]; exact hqd.ne')
  letI : Fintype ↥Rg := Fintype.ofFinite _
  letI : Field ↥Rg := (Finite.isField_of_domain ↥Rg).toField
  have hcardF : Fintype.card ↥Rg = q ^ d := by rw [Fintype.card_eq_nat_card, hcardRg]

  set T : Finset k := ((Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots).toFinset with hT
  have hpoly : (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero k (Nat.one_lt_pow hd.ne' hq1)
  have hmemT : ∀ x : k, x ∈ T ↔ x ^ (q ^ d) = x := by
    intro x
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_roots hpoly, Polynomial.IsRoot.def]
    simp [sub_eq_zero]
  have hsub : (Rg : Set k).toFinset ⊆ T := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    rw [hmemT]
    have h := FiniteField.pow_card (⟨x, hx⟩ : ↥Rg)
    rw [hcardF] at h
    have h' := congrArg Subtype.val h
    simpa using h'

  have hTcard : T.card ≤ q ^ d := by
    calc T.card ≤ Multiset.card ((Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots) :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).natDegree := Polynomial.card_roots' _
      _ = q ^ d := FiniteField.X_pow_card_sub_X_natDegree_eq k (Nat.one_lt_pow hd.ne' hq1)
  have hRgcard : ((Rg : Set k).toFinset).card = q ^ d := by
    rw [Set.toFinset_card]; convert hcardF <;> first | rfl | simp
  have heq : (Rg : Set k).toFinset = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hRgcard]; exact hTcard)
  have hcT : c ∈ T := (hmemT c).mpr hc
  rw [← heq, Set.mem_toFinset, hRgS] at hcT
  exact hcT

theorem fieldOver_le_bar' (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    NodeLocalized.fieldOver M K ≤ (modularFunctionFieldBar M).toSubfield := by
  unfold NodeLocalized.fieldOver
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨a, rfl⟩ | hy)
  · exact (modularFunctionFieldBar M).algebraMap_mem (a : AlgebraicClosure ℚ)
  · rcases hy with rfl | rfl
    · rw [← coeffEmb_jq_eq]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M (jq_mem M))
    · rw [jqNModC, ← coeffEmb_jq_eq, ← coeffEmb_qExpand_eq]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M (dvd_refl M))

theorem coeffEmb_mem_fieldOver_of_mem_full_level' (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull M) :
    coeffEmb (AlgebraicClosure ℚ) x ∈ NodeLocalized.fieldOver M K := by
  have hgen : modularFunctionFieldFull M = modularFunctionFieldC ℚ M := by
    rw [← modularFunctionFieldFullC_rat, ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero]
  rw [hgen] at hx
  change x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jqModC ℚ, jqNModC ℚ M}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | rfl | rfl
      · rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single]
        rw [← algebraMap_laurentSeries_eq_single]
        exact Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) c,
          IntermediateField.algebraMap_mem K c⟩, rfl⟩)
      · rw [jqModC_rat, coeffEmb_jq_eq]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
      · rw [jqNModC, jqModC_rat, coeffEmb_qExpand_eq, coeffEmb_jq_eq]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem coe_atkinLehnerBar_mem_fieldOver
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K) :
    ((ProlongationTuple.atkinLehnerBar N q f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := by

  have hle : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ NodeLocalized.fieldOver (N * q) K → x ∈ modularFunctionFieldBar (N * q) :=
    fun x hx => fieldOver_le_bar' (N * q) K hx

  set σ := atkinLehnerInvolutionFull N q with hσ
  suffices h : ∀ (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ NodeLocalized.fieldOver (N * q) K),
      ((ProlongationTuple.atkinLehnerBar N q ⟨x, hle x hx⟩ : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K by
    have := h (f : LaurentSeries (AlgebraicClosure ℚ)) hf
    convert this
  intro x hx
  change x ∈ Subfield.closure _ at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | rfl | rfl
      ·
        have hc : (⟨CharPReduction.constSeries K.toSubalgebra.toSubring c, hle _ (Subfield.subset_closure (Or.inl ⟨c, rfl⟩))⟩
            : ↥(modularFunctionFieldBar (N * q)))
            = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := Subtype.ext rfl
        rw [hc, ProlongationTuple.atkinLehnerBar, AlgEquiv.commutes]
        exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
      ·
        have hj : (⟨jqModC (AlgebraicClosure ℚ), hle _ (Subfield.subset_closure (Or.inr (Set.mem_insert _ _)))⟩
            : ↥(modularFunctionFieldBar (N * q)))
            = ⟨coeffEmb (AlgebraicClosure ℚ) ((⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :
                  ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ : ↥(modularFunctionFieldFull (N * q))).2⟩ :=
          Subtype.ext (coeffEmb_jq_eq).symm
        rw [hj, ProlongationTuple.atkinLehnerBar, coe_geomAut_coeffEmb]
        exact coeffEmb_mem_fieldOver_of_mem_full_level' (N * q) K (σ _).2
      · have hj : (⟨jqNModC (AlgebraicClosure ℚ) (N * q), hle _ (Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl)))⟩
            : ↥(modularFunctionFieldBar (N * q)))
            = ⟨coeffEmb (AlgebraicClosure ℚ) ((⟨qExpand ℚ (N * q) jq, jqd_mem_full (N * q) (dvd_refl _)⟩ :
                  ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (⟨qExpand ℚ (N * q) jq, jqd_mem_full (N * q) (dvd_refl _)⟩ : ↥(modularFunctionFieldFull (N * q))).2⟩ := by
          apply Subtype.ext
          show jqNModC (AlgebraicClosure ℚ) (N * q) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq)
          rw [jqNModC, ← coeffEmb_jq_eq, coeffEmb_qExpand_eq]
        rw [hj, ProlongationTuple.atkinLehnerBar, coe_geomAut_coeffEmb]
        exact coeffEmb_mem_fieldOver_of_mem_full_level' (N * q) K (σ _).2
  | one =>
      have : (⟨(1 : LaurentSeries (AlgebraicClosure ℚ)), hle _ (one_mem _)⟩ : ↥(modularFunctionFieldBar (N * q))) = 1 := rfl
      rw [this, map_one]; exact one_mem _
  | add x y hx' hy' hx hy =>
      have : (⟨x + y, hle _ (add_mem hx' hy')⟩ : ↥(modularFunctionFieldBar (N * q)))
          = ⟨x, hle _ hx'⟩ + ⟨y, hle _ hy'⟩ := rfl
      rw [this, map_add]; exact add_mem hx hy
  | neg x hx' hx =>
      have : (⟨-x, hle _ (neg_mem hx')⟩ : ↥(modularFunctionFieldBar (N * q))) = -⟨x, hle _ hx'⟩ := rfl
      rw [this, map_neg]; exact neg_mem hx
  | inv x hx' hx =>
      have : (⟨x⁻¹, hle _ (inv_mem hx')⟩ : ↥(modularFunctionFieldBar (N * q))) = (⟨x, hle _ hx'⟩)⁻¹ := rfl
      rw [this, map_inv₀]; exact inv_mem hx
  | mul x y hx' hy' hx hy =>
      have : (⟨x * y, hle _ (mul_mem hx' hy')⟩ : ↥(modularFunctionFieldBar (N * q)))
          = ⟨x, hle _ hx'⟩ * ⟨y, hle _ hy'⟩ := rfl
      rw [this, map_mul]; exact mul_mem hx hy

end SatL0

open SatL0 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (g : ↥(R.nodeIntegersOver K w)) :
    (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) ∈ Subfield.closure (Set.range (fun c : ↥(Subfield.closure (Set.range (NodeLocalized.redRestrict red K))) => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) ∧
    (R.nodeResidue₂ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) ∈ Subfield.closure (Set.range (fun c : ↥(Subfield.closure (Set.range (NodeLocalized.redRestrict red K))) => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) := by
  classical

  have hA : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    have hq : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
    rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : red ((q : ℕ) : ↥A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
    obtain ⟨u, hu'⟩ := hu
    have : red (u * u⁻¹ : (↥A)ˣ) = 1 := by rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hu', h0, zero_mul] at this
    exact zero_ne_one this

  obtain ⟨d, σ, hd, hcard, hσK, hσA⟩ :=
    ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime q A hA K

  have hcard' : Nat.card (Set.range (NodeLocalized.redRestrict red K)) = q ^ d := by
    have heq : Set.range (NodeLocalized.redRestrict red K)
        = R.redBar '' (Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1) := by
      ext c
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨⟨⟨(x : AlgebraicClosure ℚ), x.2.1⟩, x.2.2⟩, rfl⟩, R.redBar_residue _⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨⟨(a.1 : AlgebraicClosure ℚ), a.1.2, a.2⟩, (R.redBar_residue a.1).symm⟩
    rw [heq, Nat.card_image_of_injective R.redBar.injective]
    exact hcard

  set k₀ : Subfield k := Subfield.closure (Set.range (NodeLocalized.redRestrict red K)) with hk₀
  have hT : Set.range (fun c : {c : k // c ^ (q ^ d) = c} => algebraMap k ↥(modularFunctionFieldC k N) c.1)
      ⊆ Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) := by
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨c.1, Subfield.subset_closure (mem_range_redRestrict_of_pow_eq red K d hd hcard' c.1 c.2)⟩, rfl⟩
  have hmono : Subfield.closure (Set.range (fun c : {c : k // c ^ (q ^ d) = c} => algebraMap k ↥(modularFunctionFieldC k N) c.1) ∪ {(⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)), (⟨jqNModC k N, jqNModC_mem k N⟩ : ↥(modularFunctionFieldC k N))})
      ≤ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) :=
    Subfield.closure_mono (Set.union_subset_union hT subset_rfl)

  have h₁ : (g : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := g.2.1.1
  have hgK : ((g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := g.2.2
  have hfix₁ := ModularCurve.PlaceSpecialization.ProlongationTuple.arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver
    R K σ hσK d hσA (g : ↥(modularFunctionFieldBar (N * q))) h₁ hgK
  have hres₁ : R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.residue₁ ⟨(g : ↥(modularFunctionFieldBar (N * q))), h₁⟩ := rfl

  have h₂ : (g : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers := g.2.1.2.1
  have hAL₁ : ProlongationTuple.atkinLehnerBar N q (g : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers := (R.mem_integers₂_iff _).mp h₂
  have hALK := coe_atkinLehnerBar_mem_fieldOver K (g : ↥(modularFunctionFieldBar (N * q))) hgK
  have hfix₂ := ModularCurve.PlaceSpecialization.ProlongationTuple.arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver
    R K σ hσK d hσA (ProlongationTuple.atkinLehnerBar N q (g : ↥(modularFunctionFieldBar (N * q)))) hAL₁ hALK
  have hres₂ : R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.residue₁ ⟨ProlongationTuple.atkinLehnerBar N q (g : ↥(modularFunctionFieldBar (N * q))), hAL₁⟩ := by
    show R.residue₂ ⟨(g : ↥(modularFunctionFieldBar (N * q))), h₂⟩ = _
    show R.ι (R.R₂.residue ⟨(g : ↥(modularFunctionFieldBar (N * q))), h₂⟩) = R.ι (R.R₁.residue _)
    rw [R.residue₂_eq]
  refine ⟨?_, ?_⟩
  · rw [hres₁]
    exact hmono (mem_closure_of_arithFrobC_pow_smul_eq d _ hfix₁)
  · rw [hres₂]
    exact hmono (mem_closure_of_arithFrobC_pow_smul_eq d _ hfix₂)

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_mem_closure_redRestrict
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_mem_closure_redRestrict (solution)
