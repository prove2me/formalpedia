-- Prove2me | solution 1 for GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:54.459591+00:00
-- url     : https://prove2.me/submissions/79584ed3-3652-45b5-9a88-d9bdfa03da76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisMemIffNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitBallBasis
namespace GlobalTheory.UnitBallBasis
theorem _root_.solution {l : ℕ} [inst : Fact (Nat.Prime l)] {L O V : Type}
    [inst_1 : Field L] [inst_2 : Algebra ℚ_[l] L] [inst_3 : CommRing O] [inst_4 : Algebra O L]
    [inst_5 : Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hc : ∀ (a : ℤ_[l]), algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hd : ∀ (a : L), ∃ (y : ℤ_[l]), y ≠ 0 ∧ ∃ (o : O),
      algebraMap O L o = algebraMap ℚ_[l] L (y : ℚ_[l]) * a)
    [inst_8 : AddCommGroup V] [inst_9 : Module L V] [inst_10 : Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] L V] [inst_12 : Module O V] [IsScalarTower O L V]
    (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ (x : V),
      x ∈ S ↔ ∀ (i : Fin n), ‖w.repr x i‖ ≤ (1 : ℝ) := by
  classical
  have := hfree
  have : Module.Finite O S := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O S
  let c := Module.Free.chooseBasis ℤ_[l] O

  have hsm : ∀ (a : ℤ_[l]) (v : V), (algebraMap ℤ_[l] O a) • v = (a : ℚ_[l]) • v := by
    intro a v
    rw [← algebraMap_smul L (algebraMap ℤ_[l] O a) v, hc, algebraMap_smul]

  let J := Module.Free.ChooseBasisIndex ℤ_[l] O × Module.Free.ChooseBasisIndex O S
  let e : J → V := fun j => c j.1 • (b j.2 : V)
  have he : ∀ j, e j ∈ S := fun j => S.smul_mem _ (b j.2).2
  have hin : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j ∈ S := by
    intro a
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hsm]
    exact S.smul_mem _ (he j)

  have hrep : ∀ s : S, ∃ a : J → ℤ_[l], (s : V) = ∑ j, (a j : ℚ_[l]) • e j := by
    intro s
    refine ⟨fun j => c.repr (b.repr s j.2) j.1, ?_⟩
    rw [Fintype.sum_prod_type_right]
    conv_lhs => rw [← b.sum_repr s]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul]
    conv_lhs => rw [← c.sum_repr (b.repr s i)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_smul, hsm]

  have hind : ∀ a : J → ℤ_[l], ∑ j, (a j : ℚ_[l]) • e j = 0 → a = 0 := by
    intro a ha
    have h1 : ((∑ i, (∑ k, a (k, i) • c k) • b i : S) : V) = 0 := by
      rw [← ha, Fintype.sum_prod_type_right, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_smul, hsm]
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ (Submodule.coe_eq_zero.mp h1)
    funext j
    exact Fintype.linearIndependent_iff.mp c.linearIndependent _ (h3 j.2) j.1

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hli : LinearIndependent ℚ_[l] e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ‖g j‖) hl1
    have hsmall : ∀ j, ‖(l : ℚ_[l]) ^ N * g j‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (g j)) (Finset.mem_univ j)).trans hN.le
    have h0 := hind (fun j => ⟨(l : ℚ_[l]) ^ N * g j, hsmall j⟩) (by
      change ∑ j, ((l : ℚ_[l]) ^ N * g j) • e j = 0
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, hg, smul_zero])
    intro j
    have hj : (l : ℚ_[l]) ^ N * g j = 0 := congrArg Subtype.val (congrFun h0 j)
    exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))

  let P := Submodule.span ℚ_[l] (Set.range e)
  have hSP : ∀ s : S, (s : V) ∈ P := by
    intro s
    obtain ⟨a, ha⟩ := hrep s
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hLS : ∀ (x : L) (s : V), s ∈ S → x • s ∈ P := by
    intro x s hs
    obtain ⟨y, hy, o, ho⟩ := hd x
    have hy' : (y : ℚ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    have ho' : o • s = (y : ℚ_[l]) • (x • s) := by
      rw [← algebraMap_smul L o s, ho, mul_smul, algebraMap_smul]
    have hx : x • s = ((y : ℚ_[l]))⁻¹ • (o • s) := by
      rw [ho', inv_smul_smul₀ hy']
    rw [hx]
    exact P.smul_mem _ (hSP ⟨_, S.smul_mem o hs⟩)
  have hLP : ∀ (x : L) (v : V), v ∈ P → x • v ∈ P := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact hLS x _ (he j)
    | zero => rw [smul_zero]; exact P.zero_mem
    | add u w _ _ hu hw => rw [smul_add]; exact P.add_mem hu hw
    | smul q u _ hu => rw [smul_comm]; exact P.smul_mem q hu
  have hsp : ⊤ ≤ P := by
    rintro v -
    have hv : v ∈ Submodule.span L (S : Set V) := by rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv => exact hSP ⟨v, hv⟩
    | zero => exact P.zero_mem
    | add u w _ _ hu hw => exact P.add_mem hu hw
    | smul x u _ hu => exact hLP x u hu
  let b0 : Module.Basis J ℚ_[l] V := Module.Basis.mk hli hsp
  have hb0 : ∀ j, b0 j = e j := fun j => Module.Basis.mk_apply hli hsp j
  refine ⟨Fintype.card J, b0.reindex (Fintype.equivFin J), fun x => ?_⟩
  simp only [Module.Basis.repr_reindex_apply]
  constructor
  · intro hx i
    obtain ⟨a, ha⟩ := hrep ⟨x, hx⟩
    have hx0 : x = ∑ j, (a j : ℚ_[l]) • b0 j := by simpa only [hb0] using ha
    rw [hx0, congrFun (b0.repr_sum_self fun j => (a j : ℚ_[l]))]
    exact PadicInt.norm_le_one _
  · intro hx
    have hx' : ∀ j, ‖b0.repr x j‖ ≤ 1 := fun j => by simpa using hx (Fintype.equivFin J j)
    have hxs := hin fun j => ⟨b0.repr x j, hx' j⟩
    have hsum : ∑ j, ((⟨b0.repr x j, hx' j⟩ : ℤ_[l]) : ℚ_[l]) • e j = x := by
      simp_rw [← hb0]
      exact b0.sum_repr x
    rwa [hsum] at hxs
end GlobalTheory.UnitBallBasis
