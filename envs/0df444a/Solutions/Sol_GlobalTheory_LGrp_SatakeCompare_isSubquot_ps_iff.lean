-- Prove2me | solution 1 for GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:19.765564+00:00
-- url     : https://prove2.me/submissions/465a42cd-8901-4165-bf35-0b5eaa42eda0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSubquotSmIndCongr
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_deltaHalf_coe
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_delta_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_modulus_measure
import Theorems.Thm_GlobalTheory_LGrp_unrChar_eq
import Theorems.Thm_GlobalTheory_LGrp_unrTorus_apply
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_haar_conj_eq_modulus_mul
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos
import Theorems.Thm_GlobalTheory_SmGL_val_deltaHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal
namespace GlobalTheory.LGrp.SatakeCompare
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem isSubquotient_smInd_congr {G V W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {H H' : Subgroup G} (h : H = H') (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H), σ ⟨g, hg⟩ = σ' ⟨g, h ▸ hg⟩) (π : Representation ℂ G V) :
    _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H σ) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H' σ') := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g g.2
  rfl
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem blk_points (n : Type) (j : n) :
    _root_.GlobalTheory.SmGL.blk (_root_.GlobalTheory.SmGL.points n) j = j :=
  _root_.GlobalTheory.SmGL.blk_apply (_root_.GlobalTheory.SmGL.points n) j ()
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_Q_eq_parab_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).Q =
      _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  simp only [_root_.GlobalTheory.SmGL.mem_parab, blk_points]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_p_apply_eq_diag (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) (i : n) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).p q i : kˣ) : k) = (q : GL n k) i i := rfl
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem leviProj_points_eq_leviTorus_borel_p (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q)
    (hq : (q : GL n k) ∈ _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n)) :
    _root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points n) ⟨q, hq⟩ =
      _root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q) := by
  funext a
  ext i j
  rw [_root_.GlobalTheory.SmGL.leviProj_apply]
  cases i; cases j
  simp [_root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points, borelGL_p_apply_eq_diag]
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem modulus_leviEmb_eq_smGL_modulus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) (U : Subgroup (GL n k))
    (hU : U = _root_.GlobalTheory.SmGL.unipRad k e) (hc : IsClosed (U : Set (GL n k)))
    (g : _root_.GlobalTheory.SmGL.Levi k m) (x : Subgroup.normalizer (U : Set (GL n k)))
    (hx : (x : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g) :
    ((_root_.GlobalTheory.LGrp.modulus U hc x : NNReal) : ℝ) = _root_.GlobalTheory.SmGL.modulus k m g := by
  obtain ⟨x, hg⟩ := x
  simp only at hx
  subst hx
  subst hU
  letI : MeasurableSpace (_root_.GlobalTheory.SmGL.unipRad k e) := borel _
  haveI : BorelSpace (_root_.GlobalTheory.SmGL.unipRad k e) := ⟨rfl⟩
  haveI : LocallyCompactSpace (_root_.GlobalTheory.SmGL.unipRad k e) :=
    hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (_root_.GlobalTheory.SmGL.unipRad k e) := Measure.haar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    inferInstance
  have hK : MeasurableSet (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    K.isCompact.isClosed.measurableSet
  have h1 := _root_.GlobalTheory.LGrp.modulus_measure _ hc μ ⟨_, hg⟩ (K : Set _)
  have h2 := _root_.GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul k α n m e μ g _ hK
  have hset : (_root_.GlobalTheory.LGrp.conjAut (_root_.GlobalTheory.SmGL.unipRad k e) ⟨_, hg⟩) '' (K : Set _) =
      {u : _root_.GlobalTheory.SmGL.unipRad k e | ∃ s ∈ (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)),
        (u : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g * (s : GL n k) *
          (_root_.GlobalTheory.SmGL.leviEmb k e g)⁻¹} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, _root_.GlobalTheory.LGrp.conjAut_coe _ _ _⟩
    · rintro ⟨s, hs, hu⟩
      exact ⟨s, hs, Subtype.ext ((_root_.GlobalTheory.LGrp.conjAut_coe _ _ _).trans hu.symm)⟩
  rw [hset, h2] at h1
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 := (ENNReal.mul_left_inj hpos hfin).1 h1
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact ((ENNReal.ofReal_eq_ofReal_iff (_root_.GlobalTheory.SmGL.modulus_pos k g).le
    (NNReal.coe_nonneg _)).1 h3).symm
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_U_eq_unipRad_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).U = _root_.GlobalTheory.SmGL.unipRad k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  rw [_root_.GlobalTheory.LGrp.LeviDatum.mem_U,
    _root_.GlobalTheory.SmGL.mem_unipRad, ← borelGL_Q_eq_parab_points]
  constructor
  · rintro ⟨hQ, hp⟩
    refine ⟨hQ, fun a i j => ?_⟩
    have h := congrArg (fun u : kˣ => (u : k)) (congrFun hp a)
    simp only [borelGL_p_apply_eq_diag, Pi.one_apply, Units.val_one] at h
    cases i; cases j
    simpa using h
  · rintro ⟨hQ, hd⟩
    refine ⟨hQ, funext fun a => Units.ext ?_⟩
    rw [borelGL_p_apply_eq_diag]
    simpa using hd a () ()
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_s_eq_leviEmb_points_leviTorus (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (t : n → kˣ) :
    (_root_.GlobalTheory.LGrp.borelGL k n).s t =
      _root_.GlobalTheory.SmGL.leviEmb k (_root_.GlobalTheory.SmGL.points n) (_root_.GlobalTheory.SmGL.leviTorus k n t) := by
  ext i j
  change ((_root_.GlobalTheory.LGrp.diagHom k n t : GL n k) : Matrix n n k) i j = _
  rw [_root_.GlobalTheory.LGrp.diagHom_val]
  simp [_root_.GlobalTheory.SmGL.leviEmb, _root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points]
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).deltaHalf q : ℂˣ) : ℂ) =
      ((_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : n => Unit)
        (_root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q)) : ℂˣ) : ℂ) := by
  rw [_root_.GlobalTheory.LGrp.LeviDatum.deltaHalf_coe, _root_.GlobalTheory.SmGL.val_deltaHalf,
    _root_.GlobalTheory.LGrp.LeviDatum.delta_apply,
    modulus_leviEmb_eq_smGL_modulus k (_root_.GlobalTheory.SmGL.points n) _
      (borelGL_U_eq_unipRad_points k n) _ _ _ (borelGL_s_eq_leviEmb_points_leviTorus k n _)]
end GlobalTheory.LGrp.SatakeCompare
end

set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal
open GlobalTheory GlobalTheory.LGrp GlobalTheory.LGrp.SatakeCompare
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
open MeasureTheory ValuativeRel
open scoped NNReal
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.LGrp.SatakeCompare
namespace _root_.GlobalTheory.LGrp.SatakeCompare
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) :
    _root_.GlobalTheory.LGrp.IsSubquot π (_root_.GlobalTheory.LGrp.psGL k α) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π
        (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar k (α i)) := by
  change _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.LGrp.psGL k α) ↔ _
  unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd _root_.GlobalTheory.LGrp.LeviDatum.nIndQ
  unfold _root_.GlobalTheory.SmGL.prinSeries _root_.GlobalTheory.SmGL.indB _root_.GlobalTheory.SmGL.parInd
  refine isSubquotient_smInd_congr (borelGL_Q_eq_parab_points k n) _ _ (fun g hg => ?_) π
  refine LinearMap.ext fun z => ?_
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.LGrp.twist_apply,
    _root_.GlobalTheory.LGrp.charRep_apply, _root_.GlobalTheory.SmGL.twist_apply,
    _root_.GlobalTheory.SmGL.ofChar_apply]
  rw [leviProj_points_eq_leviTorus_borel_p k n ⟨g, hg⟩, borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus]
  simp [_root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.LGrp.unrTorus_apply,
    _root_.GlobalTheory.LGrp.unrChar_eq]
end _root_.GlobalTheory.LGrp.SatakeCompare
end GlobalTheory.LGrp.SatakeCompare
