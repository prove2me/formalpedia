-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fa919a75-8d3f-5660-b589-830a82eea14d

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization MazurRapoportAppendix
open scoped BigOperators

namespace DictUnfold

theorem inr_sigma_eq_iff {node : Type} (wd : node → ℕ) {n₁ n₂ : node} (a : Fin (wd n₁ - 1)) (b : Fin (wd n₂ - 1)) :
    (Sum.inr ⟨n₁, a⟩ : X0MqComponents wd) = Sum.inr ⟨n₂, b⟩ ↔ n₁ = n₂ ∧ a.val = b.val := by
  rw [Sum.inr.injEq]
  constructor
  · intro h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    exact ⟨rfl, by rw [eq_of_heq h2]⟩
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

theorem chainPos_eq_inr {node : Type} (wd : node → ℕ) (n : node) (d : ℕ) (h0 : 0 < d) (hd : d < wd n) :
    DRResolvedModelPackage.chainPos wd n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  unfold DRResolvedModelPackage.chainPos
  rw [dif_neg (by omega), dif_pos hd]

end DictUnfold

set_option maxHeartbeats 6400000 in
open Classical in

theorem DictUnfold.assembly
    (q N : ℕ) [Fact q.Prime] [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ (P.reduceFst V' ∈ W ∧ 0 < depth V' ∧ depth V' < e (P.reduceFst V')))
    (hstrict : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      ¬ (P.IsStrictFst V' ∧ P.IsStrictSnd V') ∧ (P.reduceFst V' ∈ W → ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))

    {node : Type} [Fintype node] [DecidableEq node] (wd : node → ℕ)
    (σN : ↥W ≃ node) (hσN : ∀ w : ↥W, wd (σN w) = e (w : Place k (modularFunctionFieldC k N)))

    {m : ℕ} (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents wd) (swap : Bool)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support))
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W then
           DRResolvedModelPackage.chainPos wd (σN ⟨_, hw⟩)
             (if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
         else Sum.inl 0))

    (Φ : X0MqComponents (widthOfPlaces (arithFrobC q k N) W e) ≃ X0MqComponents wd)
    (hΦ0 : Φ (Sum.inl 0) = if swap then Sum.inl 1 else Sum.inl 0)
    (hΦ1 : Φ (Sum.inl 1) = if swap then Sum.inl 0 else Sum.inl 1)
    (hΦr : ∀ (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) (kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1)) (kk' : Fin (wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) - 1)),
      (if swap then kk.val + kk'.val + 2 = wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) else kk'.val = kk.val) →
        Φ (Sum.inr ⟨s, kk⟩) = Sum.inr ⟨σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s), kk'⟩) :
    (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) *
          (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0)) =
        P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
          ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1)) ∧
    ((∑ j, if v j = Φ (Sum.inl 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) =
      Divisor.degree (P.sndDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))  := by
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩

  have hs1 : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W), (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∈ W :=
    fun s => fst_mem_of_mem_nodePairsOfPlaces s.2
  have hnEs : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W), (nodeEquivOfPlaces (arithFrobC q k N) W).symm s = ⟨_, hs1 s⟩ := fun s => rfl
  have hwd_s : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W), wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) = e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 :=
    fun s => hσN _

  have F1 : ∀ wdth kk : ℕ, kk < wdth - 1 → (if swap then wdth - 2 - kk else kk) < wdth - 1 := by
    intro wdth kk h; split_ifs <;> omega
  have F2 : ∀ wdth wdth' kk : ℕ, kk < wdth - 1 → wdth' = wdth →
      (if swap then kk + (if swap then wdth - 2 - kk else kk) + 2 = wdth' else (if swap then wdth - 2 - kk else kk) = kk) := by
    intro wdth wdth' kk h h'; split_ifs <;> omega
  have F3 : ∀ wdth d kk : ℕ, 0 < d → d < wdth → kk < wdth - 1 →
      ((if swap then wdth - d else d) - 1 = (if swap then wdth - 2 - kk else kk) ↔ d = kk + 1) := by
    intro wdth d kk h0 hd hk; split_ifs <;> omega
  have F4 : ∀ wdth d : ℕ, 0 < d → d < wdth → 0 < (if swap then wdth - d else d) ∧ (if swap then wdth - d else d) < wdth := by
    intro wdth d h0 hd; split_ifs <;> omega

  have hcls : ∀ j : Fin m,
      (P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∉ W) ∨
      (¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∉ W) ∨
      (¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W ∧
        0 < depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) < e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))) := by
    intro j
    obtain ⟨hns, hWj⟩ := hstrict _ (idx j).2
    rcases hadm _ (idx j).2 with h1 | h2 | ⟨hw, hd0, hde⟩
    · exact Or.inl ⟨h1, fun h2 => hns ⟨h1, h2⟩, fun hw => (hWj hw).1 h1⟩
    · exact Or.inr (Or.inl ⟨fun h1 => hns ⟨h1, h2⟩, h2, fun hw => (hWj hw).2 h2⟩)
    · exact Or.inr (Or.inr ⟨(hWj hw).1, (hWj hw).2, hw, hd0, hde⟩)
  have hv1 : ∀ j : Fin m, P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) → v j = (if swap then Sum.inl 1 else Sum.inl 0) := by
    intro j h; rw [hdict j, if_pos h]
  have hv2 : ∀ j : Fin m, ¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) → P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) → v j = (if swap then Sum.inl 0 else Sum.inl 1) := by
    intro j h1 h2; rw [hdict j, if_neg h1, if_pos h2]
  have hv3 : ∀ (j : Fin m) (h1 : ¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (h2 : ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W),
      v j = DRResolvedModelPackage.chainPos wd (σN ⟨_, hw⟩)
        (if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) := by
    intro j h1 h2 hw; rw [hdict j, if_neg h1, if_neg h2, dif_pos hw]

  have hbranch_ne : ∀ (b : Bool) (x : Σ n : node, Fin (wd n - 1)),
      (if b then (Sum.inl 1 : X0MqComponents wd) else Sum.inl 0) ≠ Sum.inr x ∧
      (if b then (Sum.inl 0 : X0MqComponents wd) else Sum.inl 1) ≠ Sum.inr x := by
    intro b x; cases b <;> simp
  have hbranch_ne' : ∀ b : Bool, (if b then (Sum.inl 1 : X0MqComponents wd) else Sum.inl 0) ≠ (if b then Sum.inl 0 else Sum.inl 1) := by
    intro b; cases b <;> simp

  have hB : ∀ (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) (kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1)) (j : Fin m),
      v j = Φ (Sum.inr ⟨s, kk⟩) ↔ (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) := by
    intro s kk j
    have hk : kk.val < e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 - 1 := kk.2
    have hΦ := hΦr s kk ⟨(if swap then e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 - 2 - kk.val else kk.val), lt_of_lt_of_eq (F1 _ _ hk) (by rw [hwd_s])⟩
      (F2 _ _ _ hk (hwd_s s))
    rw [hΦ]
    rcases hcls j with ⟨h1, -, hnw⟩ | ⟨h1, h2, hnw⟩ | ⟨h1, h2, hw, hd0, hde⟩
    · rw [hv1 j h1]
      constructor
      · intro h; exact absurd h (hbranch_ne swap _).1
      · rintro ⟨hr, -⟩; exact absurd (by rw [hr]; exact hs1 s) hnw
    · rw [hv2 j h1 h2]
      constructor
      · intro h; exact absurd h (hbranch_ne swap _).2
      · rintro ⟨hr, -⟩; exact absurd (by rw [hr]; exact hs1 s) hnw
    · have hwdw : wd (σN ⟨_, hw⟩) = e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) := hσN ⟨_, hw⟩
      obtain ⟨hδ0, hδ⟩ := F4 (wd (σN ⟨_, hw⟩)) (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) hd0 (by rw [hwdw]; exact hde)
      rw [hv3 j h1 h2 hw, DictUnfold.chainPos_eq_inr wd _ _ hδ0 hδ, DictUnfold.inr_sigma_eq_iff, Equiv.apply_eq_iff_eq]
      constructor
      · rintro ⟨hr0, hpos⟩
        have hr : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := congrArg Subtype.val hr0
        refine ⟨hr, ?_⟩
        have hwd' : wd (σN ⟨_, hw⟩) = e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by rw [hwdw, hr]
        change ((if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) - 1) = (if swap then e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 - 2 - kk.val else kk.val) at hpos
        rw [hwd'] at hpos
        exact (F3 _ _ _ hd0 (by rw [← hr]; exact hde) hk).1 hpos
      · rintro ⟨hr, hd⟩
        refine ⟨Subtype.ext hr, ?_⟩
        have hwd' : wd (σN ⟨_, hw⟩) = e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by rw [hwdw, hr]
        change ((if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) - 1) = (if swap then e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 - 2 - kk.val else kk.val)
        rw [hwd']
        exact (F3 _ _ _ hd0 (by rw [← hr]; exact hde) hk).2 hd

  have hC : ∀ j : Fin m, v j = Φ (Sum.inl 1) ↔ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) := by
    intro j
    rw [hΦ1]
    rcases hcls j with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, hw, hd0, hde⟩
    · rw [hv1 j h1]; exact iff_of_false (hbranch_ne' swap) h2
    · rw [hv2 j h1 h2]; exact iff_of_true rfl h2
    · have hwdw : wd (σN ⟨_, hw⟩) = e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) := hσN ⟨_, hw⟩
      obtain ⟨hδ0, hδ⟩ := F4 (wd (σN ⟨_, hw⟩)) (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) hd0 (by rw [hwdw]; exact hde)
      rw [hv3 j h1 h2 hw, DictUnfold.chainPos_eq_inr wd _ _ hδ0 hδ]
      exact iff_of_false (hbranch_ne swap _).2.symm h2

  have hdeg1 : ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), Divisor.degree D = D.sum (fun _ n => n) := by
    intro D
    show Finsupp.liftAddHom (fun v => AddMonoidHom.mulRight ((v.deg : ℕ) : ℤ)) D = _
    rw [Finsupp.liftAddHom_apply]
    refine Finsupp.sum_congr (fun v _ => ?_)
    show D v * ((v.deg : ℕ) : ℤ) = D v
    rw [ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) v, Nat.cast_one, mul_one]

  have hreidx : ∀ f : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℤ, (∑ j : Fin m, f (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) = ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, f V := by
    intro f
    calc (∑ j : Fin m, f (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) = ∑ V : ↥((D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support), f (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :=
          Fintype.sum_equiv idx (fun j => f (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (fun V => f (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (fun j => rfl)
      _ = ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, f V := Finset.sum_coe_sort _ _
  refine ⟨?_, ?_⟩
  ·
    intro s
    have hinner : ∀ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1),
        (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0) =
        ∑ j, if (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0 := by
      intro kk
      exact Finset.sum_congr rfl (fun j _ => if_congr (hB s kk j) rfl rfl)
    have hcollapse : ∀ j : Fin m,
        (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) * (if (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0)) =
        if P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 then ((pos j : ℤ) - (neg j : ℤ)) * (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℤ) else 0 := by
      intro j
      by_cases hr : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
      · rw [if_pos hr]
        obtain ⟨hw, hd0, hde⟩ : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W ∧ 0 < depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) < e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) := by
          rcases hcls j with ⟨-, -, hnw⟩ | ⟨-, -, hnw⟩ | ⟨-, -, h⟩
          · exact absurd (by rw [hr]; exact hs1 s) hnw
          · exact absurd (by rw [hr]; exact hs1 s) hnw
          · exact h
        rw [hr] at hde
        have hdlt : depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - 1 < widthOfPlaces (arithFrobC q k N) W e s - 1 := by
          show depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - 1 < e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 - 1; omega
        rw [Finset.sum_eq_single ⟨depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - 1, hdlt⟩]
        · have hcast : (((depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - 1 : ℕ) : ℤ) + 1) = (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℤ) := by omega
          rw [if_pos ⟨hr, by simp only [Fin.val_mk]; omega⟩]
          show (((depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - 1 : ℕ) : ℤ) + 1) * ((pos j : ℤ) - (neg j : ℤ)) = ((pos j : ℤ) - (neg j : ℤ)) * (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℤ)
          rw [hcast, mul_comm]
        · intro kk _ hne
          have hno : ¬ (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) :=
            fun h => hne (Fin.ext (by simp only [Fin.val_mk]; omega))
          rw [if_neg hno, mul_zero]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      · rw [if_neg hr]
        refine Finset.sum_eq_zero (fun kk _ => ?_)
        rw [if_neg (fun h => hr h.1), mul_zero]
    calc (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) * (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0))
        = ∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ∑ j, ((kk : ℤ) + 1) * (if (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) := by
          refine Finset.sum_congr rfl (fun kk _ => ?_)
          rw [hinner kk, Finset.mul_sum]
      _ = ∑ j, ∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) * (if (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∧ depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = kk.val + 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) :=
          Finset.sum_comm
      _ = ∑ j, (if P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 then ((pos j : ℤ) - (neg j : ℤ)) * (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℤ) else 0) :=
          Finset.sum_congr rfl (fun j _ => hcollapse j)
      _ = ∑ j, (if P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) * (depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ℤ) else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmult j]
      _ = ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, (if P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V * (depth V : ℤ) else 0) :=
          hreidx (fun V => if P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V * (depth V : ℤ) else 0)
      _ = P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by
          unfold PlaceSpecialization.depthDiv
          rw [Finsupp.sum_apply, Finsupp.sum]
          refine Finset.sum_congr rfl (fun V _ => ?_)
          rw [Finsupp.single_apply]
  ·
    have hinner : (∑ j, if v j = Φ (Sum.inl 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) = ∑ j, if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then ((pos j : ℤ) - (neg j : ℤ)) else 0 :=
      Finset.sum_congr rfl (fun j _ => if_congr (hC j) rfl rfl)
    rw [hinner, hdeg1, Finsupp.sum]
    unfold PlaceSpecialization.sndDiv
    rw [Finsupp.support_filter, Finset.sum_filter]
    calc (∑ j, if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then ((pos j : ℤ) - (neg j : ℤ)) else 0)
        = ∑ j, (if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmult j]
      _ = ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, (if P.IsStrictSnd V then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V else 0) := hreidx (fun V => if P.IsStrictSnd V then (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V else 0)
      _ = ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, (if P.IsStrictSnd V then (Finsupp.filter P.IsStrictSnd (D₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V else 0) := by
          refine Finset.sum_congr rfl (fun V _ => ?_)
          by_cases hV : P.IsStrictSnd V
          · rw [if_pos hV, if_pos hV, Finsupp.filter_apply_pos _ _ hV]
          · rw [if_neg hV, if_neg hV]

set_option maxHeartbeats 1600000 in
open Classical in

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ (P.reduceFst V' ∈ W ∧ 0 < depth V' ∧ depth V' < e (P.reduceFst V')))
    (hstrict : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      ¬ (P.IsStrictFst V' ∧ P.IsStrictSnd V') ∧ (P.reduceFst V' ∈ W → ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))

    {node : Type} [Fintype node] [DecidableEq node] (wd : node → ℕ)
    (σN : ↥W ≃ node) (hσN : ∀ w : ↥W, wd (σN w) = e (w : Place k (modularFunctionFieldC k N)))

    {m : ℕ} (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents wd) (swap : Bool)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support))
    (hmult : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ W then
           DRResolvedModelPackage.chainPos wd (σN ⟨_, hw⟩)
             (if swap then wd (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
         else Sum.inl 0))

    (Φ : X0MqComponents (widthOfPlaces (arithFrobC q k N) W e) ≃ X0MqComponents wd)
    (hΦ0 : Φ (Sum.inl 0) = if swap then Sum.inl 1 else Sum.inl 0)
    (hΦ1 : Φ (Sum.inl 1) = if swap then Sum.inl 0 else Sum.inl 1)
    (hΦr : ∀ (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) (kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1)) (kk' : Fin (wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) - 1)),
      (if swap then kk.val + kk'.val + 2 = wd (σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s)) else kk'.val = kk.val) →
        Φ (Sum.inr ⟨s, kk⟩) = Sum.inr ⟨σN ((nodeEquivOfPlaces (arithFrobC q k N) W).symm s), kk'⟩) :
    (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      (∑ kk : Fin (widthOfPlaces (arithFrobC q k N) W e s - 1), ((kk : ℤ) + 1) *
          (∑ j, if v j = Φ (Sum.inr ⟨s, kk⟩) then ((pos j : ℤ) - (neg j : ℤ)) else 0)) =
        P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
          ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1)) ∧
    ((∑ j, if v j = Φ (Sum.inl 1) then ((pos j : ℤ) - (neg j : ℤ)) else 0) =
      Divisor.degree (P.sndDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by
  exact DictUnfold.assembly q N P W e depth D₀ hadm hstrict wd σN hσN pos neg v swap idx hmult hdict Φ hΦ0 hΦ1 hΦr

end S_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_sum_height_mul_multidegree_comp_eq_depthDiv_and_apply_inl_one_eq_degree_sndDiv_level (solution)
