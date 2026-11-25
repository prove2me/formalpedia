-- Prove2me | solution 1 for GlobalTheory.AbLaw.exists_tw_extend_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:59.876925+00:00
-- url     : https://prove2.me/submissions/a1d8b887-62ec-4f60-85d7-cda170d0d0c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_basicOpen_rs_eq
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_fun_extend
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_fun_kill
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_exists_fin_cover
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_unit_shift
import Theorems.Thm_GlobalTheory_AbLaw_TwExtend_pw_rel
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_of_local
import Theorems.Thm_GlobalTheory_AbLaw_isLB_tw
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
open TwExtend
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → QuasiSeparatedSpace Y → ∀ y : SecOn (tw M H t) V, ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l)) (SecOn.twCoord a p l) = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord y p l := by
  intro Y H M d σ V t hH hM hV _ _ y
  obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, H.U l), ∀ l, u l = σ.f l := ⟨σ.f, fun _ => rfl⟩
  have hb : ∀ l {W : Y.Opens} (h : W ≤ H.U l), Y.basicOpen (rs Y h (u l)) = V ⊓ W := by
    intro l W h
    rw [hu, hV]
    exact basicOpen_rs_eq σ l h
  have hrel := pw_rel σ u hu
  suffices key : ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι),
      rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l))
        (SecOn.twCoord a p l) =
      rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (u l) ^ k *
        SecOn.twCoord y p l by
    simp only [hu] at key
    exact key
  clear hu hV σ
  obtain ⟨κ, _, W, p, l, hW, hWc, hc⟩ := exists_fin_cover hM hH
  have hWl : ∀ a, W a ≤ H.U (l a) := fun a => (hWc a).trans inf_le_right
  have hWp : ∀ a, W a ≤ M.U (p a) := fun a => (hWc a).trans inf_le_left
  choose n x hx using fun a => fun_extend (hW a) (rs Y (hWl a) (u (l a))) (hb _ _) inf_le_right
    (rs Y (inf_le_inf_left V (hWc a)) (SecOn.twCoord y (p a) (l a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N :=
    ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ∀ a, Γ(Y, W a), ∀ a {O : Y.Opens} (hO : O ≤ W a) (hO' : O ≤ V),
      rs Y hO (x' a) = rs Y (hO.trans (hWl a)) (u (l a)) ^ N *
        rs Y (le_inf hO' (hO.trans (hWc a))) (SecOn.twCoord y (p a) (l a)) := by
    refine ⟨fun a => rs Y (hWl a) (u (l a)) ^ (N - n a) * x a, fun a O hO hO' => ?_⟩
    have := congrArg (rs Y (le_inf hO' hO)) (hx a)
    simp only [map_mul, map_pow, rs_rs] at this ⊢
    rw [this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  have hk : ∀ q : κ × κ, ∃ K : ℕ, rs Y (inf_le_left.trans (hWl q.1)) (u (l q.1)) ^ K *
      (rs Y (inf_le_left : W q.1 ⊓ W q.2 ≤ _) (x' q.1) -
        (res (inf_le_inf (hWp q.1) (hWp q.2)) (M.g (p q.1) (p q.2)) *
          res (inf_le_inf (hWl q.1) (hWl q.2)) (H.g (l q.1) (l q.2)) ^ (t + N * d)).val *
        rs Y inf_le_right (x' q.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) _ _ (hb _ _) inf_le_right ?_
    have hM' : V ⊓ (W a ⊓ W b) ≤ M.U (p a) ⊓ M.U (p b) :=
      inf_le_right.trans (inf_le_inf (hWp a) (hWp b))
    have hH' : V ⊓ (W a ⊓ W b) ≤ H.U (l a) ⊓ H.U (l b) :=
      inf_le_right.trans (inf_le_inf (hWl a) (hWl b))
    have e : rs Y (inf_le_right : V ⊓ (W a ⊓ W b) ≤ W a ⊓ W b)
        (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b)) *
          res (inf_le_inf (hWl a) (hWl b)) (H.g (l a) (l b)) ^ (t + N * d)).val =
        (res hM' (M.g (p a) (p b)) * res hH' (H.g (l a) (l b)) ^ (t + N * d)).val := by
      refine (GlobalTheory.LB.val_res _ _).symm.trans (congrArg Units.val ?_)
      rw [map_mul, map_zpow, LB.res_res, LB.res_res]
    rw [map_sub, map_mul, e, rs_rs, rs_rs, hx' a _ inf_le_left, hx' b _ inf_le_left,
      SecOn.twCoord_compat y (p a) (p b) (l a) (l b) _
        (inf_le_inf_left V (inf_le_right.trans (hWc b))) hM' hH', ← _root_.mul_assoc,
      ← _root_.mul_assoc, unit_shift _ _ t d N (hrel (l a) (l b) (hH'.trans inf_le_left) _ hH'),
      sub_self]
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ q, k q ≤ K :=
    ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  have hNK : t + ((N + K : ℕ) : ℤ) * d = t + N * d + K * d := by push_cast; ring
  obtain ⟨s, hs, -⟩ := SecOn.existsUnique_of_local (isLB_tw hM hH (t + ((N + K : ℕ) : ℤ) * d))
    (V := ⊤) W (fun _ => le_top) hc (fun a => (p a, l a)) hWc
    (fun a => rs Y (hWl a) (u (l a)) ^ K * x' a) (fun a b => by
      have e := congrArg Units.val (SecOn.res_tw_g (M := M) (H := H)
        (t + ((N + K : ℕ) : ℤ) * d) (p a) (p b) (l a) (l b) (inf_le_inf (hWc a) (hWc b))
        (inf_le_inf (hWp a) (hWp b)) (inf_le_inf (hWl a) (hWl b)))
      refine Eq.trans ?_ (congrArg (· * rs Y (inf_le_right : W a ⊓ W b ≤ W b)
        (rs Y (hWl b) (u (l b)) ^ K * x' b)) e.symm)
      have h0 := hk (a, b)
      have h1 := unit_shift (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b))) _ (t + N * d) d K
        (hrel (l a) (l b) (inf_le_left.trans (hWl a)) (inf_le_right.trans (hWl b))
          (inf_le_inf (hWl a) (hWl b)))
      simp only [map_mul, map_pow, rs_rs]
      rw [hNK, ← _root_.mul_assoc, h1, ← Nat.sub_add_cancel (hK (a, b)), pow_add]
      linear_combination
        rs Y (inf_le_left.trans (hWl a) : W a ⊓ W b ≤ _) (u (l a)) ^ (K - k (a, b)) * h0)
  refine ⟨N + K, s, fun q m => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun a => V ⊓ (M.U q ⊓ H.U m) ⊓ W a) (fun _ => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf (top_unique hc) _) fun a => ?_
  change rs Y _ _ = rs Y _ _
  have hM' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ M.U q ⊓ M.U (p a) :=
    inf_le_inf (inf_le_right.trans inf_le_left) (hWp a)
  have hH' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ H.U m ⊓ H.U (l a) :=
    inf_le_inf (inf_le_right.trans inf_le_right) (hWl a)
  have hs' : rs Y (le_inf le_top (hWc a)) (SecOn.twCoord s (p a) (l a)) =
    rs Y (hWl a) (u (l a)) ^ K * x' a := hs a
  have e := congrArg (rs Y (inf_le_right : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ W a)) hs'
  rw [map_mul, map_pow, rs_rs, rs_rs, hx' a _ (inf_le_left.trans inf_le_left),
    ← _root_.mul_assoc, ← pow_add, add_comm K N] at e
  rw [map_mul, map_pow, rs_rs, rs_rs,
    SecOn.twCoord_compat s q (p a) m (l a) _ (le_inf le_top (inf_le_right.trans (hWc a))) hM' hH',
    SecOn.twCoord_compat y q (p a) m (l a) _
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (hWc a))) hM' hH',
    e, ← _root_.mul_assoc, ← _root_.mul_assoc,
    unit_shift _ _ t d (N + K) (hrel m (l a) (hH'.trans inf_le_left) _ hH')]
end GlobalTheory.AbLaw
