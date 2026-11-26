-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.auxiliaryReadoutsOfCertificates
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:28:52.29041+00:00
-- url     : https://prove2.me/submissions/adb898ac-81d6-459e-a28c-8e404b022516

import Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors

open Matrix
open scoped Kronecker
namespace IntMul.Kappa.DeferredReadout
theorem gram_apply (x y : V) :
    gramForm x y = 9 * (x ⬝ᵥ y) - total x * total y := rfl

theorem gram_symm (x y : V) : gramForm x y = gramForm y x := by
  rw [gram_apply, gram_apply, dotProduct_comm x y, mul_comm (total x) (total y)]

theorem gram_refl : gramForm.IsRefl := by
  intro x y h
  rwa [gram_symm]

private theorem sum_mem (tbl : RowTable) (B : Frame) (terms : List (Nat × Int))
    (hin : ∀ k ∈ terms, k.1 ∈ B) :
    (fun j : Fin 23 => (combination tbl terms j.val : ℚ)) ∈ space 23 tbl B := by
  induction terms with
  | nil => exact (space 23 tbl B).zero_mem
  | cons term rest ih =>
    rcases term with ⟨r,c⟩
    have hr : row 23 tbl r ∈ space 23 tbl B :=
      Submodule.subset_span ⟨r, hin (r,c) (.head _), rfl⟩
    have hs := ih (fun k hk => hin k (.tail _ hk))
    convert (space 23 tbl B).add_mem ((space 23 tbl B).smul_mem (c : ℚ) hr) hs using 1
    funext j
    simp [combination, row, Pi.smul_apply]

theorem gramCertificate_sound (tbl : RowTable) (B : Frame) (c : GramCertificate)
    (hc : c.ok tbl B = true) : IsCompl (space 23 tbl B) (gramForm.orthogonal (space 23 tbl B)) := by
  simp only [GramCertificate.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, beq_iff_eq] at hc
  let w : V := fun j => (c.coord j : ℚ)
  have hw : w ∈ space 23 tbl B := by
    have eqn : w = fun j : Fin 23 => (combination tbl c.terms j.val : ℚ) := by
      funext j
      change (c.coord j : ℚ) = (combination tbl c.terms j.val : ℚ)
      exact_mod_cast hc.1.2 j (List.mem_finRange j)
    rw [eqn]
    exact sum_mem tbl B c.terms hc.1.1.2
  let law := gramForm.flip w - (c.den : ℚ) • total
  have hlo : space 23 tbl B ≤ LinearMap.ker law := by
    apply Submodule.span_le.mpr
    rintro x ⟨r,hr,rfl⟩
    change gramForm (row 23 tbl r) w - (c.den : ℚ) * total (row 23 tbl r) = 0
    apply sub_eq_zero.mpr
    rw [gram_apply]
    simp only [total, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, row, w]
    exact_mod_cast hc.2 r hr
  apply gramForm.isCompl_orthogonal_iff_disjoint gram_refl |>.2
  apply Submodule.disjoint_def.mpr
  intro x hx ho
  have hzero : gramForm x w = 0 := by rw [gram_symm]; exact ho w hw
  have hxlaw : gramForm x w - (c.den : ℚ) * total x = 0 := hlo hx
  have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc.1.1.1
  have hs : total x = 0 := by
    rw [hzero, zero_sub, neg_eq_zero] at hxlaw
    exact (mul_eq_zero.mp hxlaw).resolve_left hd
  have hxx := ho x hx
  rw [gram_apply, hs, zero_mul, sub_zero] at hxx
  exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp hxx).resolve_left (by norm_num))

theorem project_absorbs {U W : Subspace} (incl : U ≤ W)
    (hu : IsCompl U (gramForm.orthogonal U)) (hw : IsCompl W (gramForm.orthogonal W)) :
    project W * project U = project U := by
  classical
  simp only [project, dif_pos hu, dif_pos hw, ← LinearMap.toMatrix'_comp]
  apply congrArg (fun f : V →ₗ[ℚ] V => LinearMap.toMatrix' f)
  apply LinearMap.ext
  intro x
  exact Submodule.projection_apply_of_mem_left hw (incl (Submodule.projection_apply_mem hu x))

private theorem complement_one {R : Type*} [Ring R] {L E : R} (h : L * E = E) :
    (1-L)*(1-E) = 1-L := by
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

private theorem complement_two {R : Type*} [Ring R] {L E : R} (h : L * E = L) :
    (1-L)*(1-E) = 1-E := by
  rw [sub_mul, one_mul, mul_sub, mul_one, h, sub_self, sub_zero]

theorem aux_absorbs {E L T : Mat} (h : L * E = E) (ht : T*T=T) :
    aux L T * aux E T = aux E T := by
  apply complement_two
  rw [← Matrix.mul_kronecker_mul, complement_one h, ht]

theorem target_idempotent (t : V) : targetProjector t * targetProjector t = targetProjector t := by
  classical
  unfold targetProjector
  rw [vecMulVec_mul_vecMulVec, smul_dotProduct]
  by_cases h : targetCovector t ⬝ᵥ t = 0
  · simp [h]
  · simp [smul_eq_mul, h]

theorem triple_count : targetTriples.size = 1771 := by decide +kernel

theorem all_complements (d : Block) (cs : Array GramCertificate) (hg : gramChecks d cs = true)
    (hb : eventFrameBounds d = true) (i : Fin d.targets.size) :
    ∀ U ∈ d.targets[i.val].map d.atEvent, IsCompl U (gramForm.orthogonal U) := by
  intro U h
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
  have ht := List.all_eq_true.mp hb d.targets[i.val] (Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt))
  have hi := of_decide_eq_true (List.all_eq_true.mp ht e he)
  exact gramCertificate_sound d.entry (d.basis e.frame) _
    (List.all_eq_true.mp hg e.frame (List.mem_range.mpr hi))

theorem edges_of_frames (fs : List Subspace) (t : V)
    (hc : ∀ U ∈ fs, IsCompl U (gramForm.orthogonal U)) (hn : fs.Pairwise (· ≤ ·)) :
    (readoutEdges fs t).Pairwise (fun early late => late * early = early) := by
  apply List.pairwise_map.mpr
  apply hn.imp_of_mem
  intro U W hu hw h
  exact aux_absorbs (project_absorbs h (hc U hu) (hc W hw)) (target_idempotent t)


end IntMul.Kappa.DeferredReadout

open IntMul.Kappa.DeferredReadout

theorem solution (d : Block) (cert : Nat → GramCertificate) (es : List Event) (t : V)
    (hg : ∀ i, i < d.frames.size → (cert i).ok d.entry (d.basis i) = true)
    (hb : ∀ e ∈ es, e.frame < d.frames.size)
    (hn : (es.map d.atEvent).Pairwise (· ≤ ·)) :
    (∀ U ∈ es.map d.atEvent, IsCompl U (gramForm.orthogonal U)) ∧
    (readoutEdges (es.map d.atEvent) t).Pairwise (fun earlier later => later * earlier = earlier) := by
  have hc : ∀ U ∈ es.map d.atEvent, IsCompl U (gramForm.orthogonal U) := by
    intro U hU
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hU
    exact gramCertificate_sound d.entry (d.basis e.frame) (cert e.frame) (hg e.frame (hb e he))
  exact ⟨hc, edges_of_frames _ _ hc hn⟩
