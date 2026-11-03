-- Prove2me | solution 1 for HnEpsData.central_trivial_virtually_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:23:03.942816+00:00
-- url     : https://prove2.me/submissions/b8705064-71ac-4d48-b77d-77c0a7fc24d6

import Mathlib
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001
import Theorems.Thm_HnEpsData_H_n_contradiction
import Theorems.Thm_poly_growth_equiv

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_Closure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroup closures

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


open scoped Pointwise Finset

-- TODO - deduplicate with with 'mem_S_prod_list'
lemma mem_closure_prod_list {G: Type*} [Group G] (S: Set G) (S_eq_Sinv: S = S⁻¹) (x: G) (hx: x ∈ Subgroup.closure S): ∃ l: List S, l.unattach.prod = x := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  specialize foo hx
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  conv at mem_s =>
    intro y hy
    rw [← S_eq_Sinv]
    simp
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold List.unattach
  simp [prod_eq]
end

section
-- module Solutions.OAIQ093_PR.Unitary_CentralTrivial
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The centrally trivial case

`H_n_contradiction` and `central_trivial_virtually_abelian`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]


open scoped Pointwise

-- TODO - figure out why this causes a diamond when we use 'open Classical'


-- Theorem 3.8, case with only trivial elements in the center
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2200000 in
lemma central_trivial_virtually_abelian_oai (n : ℕ) (hn : 2 ≤ n) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
  (G'_central_trivial : ∀ g : (G' n (H_n_eps hn) G), g ∈ Set.center (G' n (H_n_eps hn) G) → ∃ z : ℂ, g.val.val.val = z • 1)
  (G'_finite_index: (G' n (H_n_eps hn) G).FiniteIndex)
  (S_poly_data: SPolyData (G' n (H_n_eps hn) G))
  -- This parameter is kind of hack - ideally, we would refactor so that just 'h_n_eps_data' is enough
  (data_eq_degree: h_n_eps_data.degree = S_poly_data.S_poly_deg)
  : ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by

  classical

  by_cases all_mul_identity : ∀ h : (G' n (H_n_eps hn) G), ∃ z : ℂ, h.val.val.val = z • 1
  · use (G' n (H_n_eps hn) G)
    refine ⟨?_, ?_⟩
    · refine { is_comm := ?_ }
      refine { comm := ?_ }
      intro a b
      have a_diag := all_mul_identity a
      have b_diag := all_mul_identity b
      obtain ⟨a_z, a_eq⟩ := a_diag
      obtain ⟨b_z, b_eq⟩ := b_diag
      ext i j
      simp
      rw [a_eq, b_eq]
      simp
      group
    · infer_instance
  ·
    simp [-Subtype.forall, -Subtype.exists] at all_mul_identity
    obtain ⟨x, hx⟩ := all_mul_identity

    have G_fg: Group.FG G := by
      exact (Group.fg_iff_subgroup_fg G).mpr G_FG


    let S' := S_poly_data.S
    have S'_finite := S_poly_data.S_finite

    -- Add identity and inverses to S' to make things easier
    let S'' := S'
    have S''_finite: Set.Finite S'' := by
      dsimp [S'']
      apply S'_finite


    have S''_eq_S''inv: S'' = S''⁻¹ := by
      unfold S''
      apply S_poly_data.S_inv


    have S''_generates: Subgroup.closure S'' = ⊤ := by
      dsimp [S'']
      apply S_poly_data.S_generates


    have s_list (s: S'') := (mem_closure_prod_list ((Metric.ball (1 : G) (H_n_eps hn)) ∪ (Metric.ball (1 : G) (H_n_eps hn))⁻¹) (by
      simp
      rw [Set.union_comm]
    ) s (by
      have s_prop := s.val.property
      simp only [G'] at s_prop
      rw [Subgroup.closure_union]
      simp [s_prop]
    ))

    -- Write each element in S'' as a product of elements of S', and then collect all of the used elements into a set
    -- We may need to manually union this with S⁻¹, since the inverse of the produces
    -- could be chosen to be built with different elements (not the inverses of the ones in the original list)
    let pre_S := ⋃ s : S''_finite.toFinset, ((s_list ⟨s, by (
      have foo := s.property
      rw [Set.Finite.mem_toFinset] at foo
      exact foo
    )⟩).choose.unattach.toFinset : Set ↥G) ∪ {1}
    let S := pre_S ∪ pre_S⁻¹ ∪ {1}

    have S_dist: ∀ s ∈ S, ‖s.val.val - 1‖ < H_n_eps hn := by
      intro s hs
      dsimp [S] at hs

      rw [Set.union_assoc] at hs
      cases hs
      . rename_i s_mem
        dsimp [pre_S] at s_mem
        rw [Set.mem_iUnion] at s_mem
        obtain ⟨y, y_mem⟩ := s_mem
        simp only [List.coe_toFinset, List.mem_unattach, Set.mem_union, Set.mem_inv,
          Set.mem_setOf_eq] at y_mem
        obtain ⟨s_mem_S'', s_mem_choose⟩ := y_mem
        simp at s_mem_S''
        simp only [Subtype.dist_eq, dist_eq_norm_sub] at s_mem_S''
        conv at s_mem_S'' =>
          right
          arg 1
          arg 1
          equals (star s.val.val * 1 - (star s.val.val) * s.val.val) =>
            simp

        rw [← mul_sub] at s_mem_S''
        rw [← Unitary.coe_star] at s_mem_S''
        rw [CStarRing.norm_coe_unitary_mul] at s_mem_S''
        nth_rw 2 [norm_sub_rev] at s_mem_S''
        simp at s_mem_S''
        . exact s_mem_S''
        .
          rename_i s_eq_one
          simp at s_eq_one
          simp [s_eq_one]
          have foo := H_n_eps_pos hn
          linarith
      .
        -- TODO - deduplicate most of this with the above case
        rename_i s_mem
        rw [Set.union_comm] at s_mem
        cases s_mem
        . rename_i s_mem_one
          simp at s_mem_one
          simp [s_mem_one]
          apply H_n_eps_pos

        rename_i s_mem
        dsimp [pre_S] at s_mem
        rw [Set.iUnion_inv] at s_mem
        rw [Set.mem_iUnion] at s_mem
        obtain ⟨y, y_mem⟩ := s_mem
        simp only [List.coe_toFinset, List.mem_unattach, Set.mem_union, Set.mem_inv,
          Set.mem_setOf_eq] at y_mem
        obtain ⟨s_mem_S'', s_mem_choose⟩ := y_mem
        simp at s_mem_S''
        simp only [Subtype.dist_eq, dist_eq_norm_sub] at s_mem_S''
        rw [or_comm] at s_mem_S''
        conv at s_mem_S'' =>
          right
          arg 1
          arg 1
          equals (star s.val.val * 1 - (star s.val.val) * s.val.val) =>
            simp

        rw [← mul_sub] at s_mem_S''
        rw [← Unitary.coe_star] at s_mem_S''
        rw [CStarRing.norm_coe_unitary_mul] at s_mem_S''
        nth_rw 2 [norm_sub_rev] at s_mem_S''
        simp at s_mem_S''
        . exact s_mem_S''
        .
          rename_i s_eq_one
          simp at s_eq_one
          simp [s_eq_one]
          have foo := H_n_eps_pos hn
          linarith


    have S_finite: Set.Finite S := by
      dsimp [S]
      apply Set.Finite.union
      .
        simp
        dsimp [pre_S]
        apply Set.Finite.sUnion
        .
          apply Set.finite_range
        .
          intro y hy
          rw [Set.mem_range] at hy
          obtain ⟨x, x_mem, y_eq⟩ := hy
          apply Set.Finite.union
          . apply Finset.finite_toSet
          . simp
      . simp

    have S_union_Sinv: S ∪ S⁻¹ = S := by
      dsimp [S]
      simp [-Set.union_singleton]
      grind

    have S_eq_Sinv: S = S⁻¹ := by
      rw [← S_union_Sinv]
      simp
      rw [Set.union_comm]

    have S_generates: Subgroup.closure S = (G' n (H_n_eps hn) G) := by

      ext a
      unfold S
      rw [Subgroup.closure_union]
      simp
      rw [Subgroup.closure_union]
      simp
      unfold pre_S
      refine ⟨?_, ?_⟩
      . intro ha
        -- TODO - only the 'mem' case is non-trivial. We probably don't actually need a full induction proof
        induction ha using Subgroup.closure_induction with
        | one =>
          simp [G']
        | mem x hx =>
          rw [Set.mem_iUnion] at hx
          obtain ⟨y, y_mem⟩ := hx
          have y_prop := y.property
          rw [Set.Finite.mem_toFinset] at y_prop
          cases y_mem
          .
            rename_i y_mem
            simp at y_mem
            obtain ⟨x_dist, x_mem⟩ := y_mem
            simp [G']
            apply Subgroup.mem_closure_of_mem
            simp
            cases x_dist
            . rename_i x_dist_le
              exact x_dist_le
            . rename_i x_inv_dist

              -- TODO - deduplicate this, in particular the 'CStarRing.norm_coe_unitary_mul' code
              simp only [Subtype.dist_eq, dist_eq_norm_sub] at x_inv_dist
              conv at x_inv_dist =>
                lhs
                arg 1
                equals (star x.val.val * 1 - (star x.val.val) * x.val.val) =>
                  simp

              rw [← mul_sub] at x_inv_dist
              rw [← Unitary.coe_star] at x_inv_dist
              rw [CStarRing.norm_coe_unitary_mul] at x_inv_dist
              rw [norm_sub_rev] at x_inv_dist
              simp only [Subtype.dist_eq, dist_eq_norm_sub]
              exact x_inv_dist
          .
            rename_i x_mem_one
            simp at x_mem_one
            simp [x_mem_one]
        | mul x y hx hy x_mem y_mem =>
          apply Subgroup.mul_mem
          . exact x_mem
          . exact y_mem
        | inv x hx x_mem =>
          apply Subgroup.inv_mem
          exact x_mem
      .
        intro ha
        apply_fun (Subgroup.map (G' n (H_n_eps hn) G).subtype) at S''_generates
        conv at S''_generates =>
          rhs
          equals (G' n (H_n_eps hn) G) =>
            ext a
            simp

        rw [← S''_generates] at ha
        simp at ha
        obtain ⟨a_mem_g', a_mem_closure⟩ := ha
        rw [← Subgroup.mem_toSubmonoid] at a_mem_closure
        rw [Subgroup.closure_toSubmonoid] at a_mem_closure
        obtain ⟨l, l_mem, l_prod_eq⟩ := Submonoid.exists_list_of_mem_closure a_mem_closure
        rw [Subtype.ext_iff] at l_prod_eq
        simp at l_prod_eq
        rw [← l_prod_eq]
        apply Subgroup.list_prod_mem
        intro x x_mem_l
        simp at x_mem_l
        obtain ⟨x_mem_g', x_mem_l⟩ := x_mem_l
        have x_mem_ball := l_mem _ x_mem_l

        rw [Subgroup.closure_iUnion]
        rw [← S''_eq_S''inv] at x_mem_ball
        simp at x_mem_ball
        apply Subgroup.mem_iSup_of_mem (i := ⟨⟨x, x_mem_g'⟩, (by simp; apply x_mem_ball)⟩)
        have my_spec := (s_list  ⟨⟨x, x_mem_g'⟩, x_mem_ball⟩).choose_spec
        simp at my_spec
        conv =>
          arg 2
          rw [← my_spec]

        apply Subgroup.list_prod_mem
        intro b b_mem
        apply Subgroup.mem_closure_of_mem
        apply Set.mem_union_left
        simpa using b_mem


    have nontrivial_h: ∃ h: S, ∀ z: ℂ,  h.val.val.val ≠ z • 1 := by
      by_contra!

      have x_mem_closure: x.val ∈ Subgroup.closure S := by
        rw [S_generates]
        simp


      rw [← Subgroup.mem_toSubmonoid] at x_mem_closure
      rw [Subgroup.closure_toSubmonoid] at x_mem_closure
      obtain ⟨l, l_mem, l_prod_eq⟩ := Submonoid.exists_list_of_mem_closure x_mem_closure
      simp_rw [S_union_Sinv] at l_mem

      have list_prod_trivial: ∃ z: ℂ, l.unattach.unattach.prod = z • 1 := by
        apply List.prod_induction (p := fun a => ∃ z: ℂ, a = z • 1)
        .
          intro a b a_diag b_diag
          obtain ⟨a_z, a_eq⟩ := a_diag
          obtain ⟨b_z, b_eq⟩ := b_diag
          use b_z * a_z
          rw [a_eq, b_eq]
          rw [mul_smul]
          simp
        . use 1
          simp
        .
          intro x x_mem
          rw [List.mem_unattach] at x_mem
          obtain ⟨a, ha⟩ := x_mem
          rw [List.mem_unattach] at ha
          obtain ⟨b, hb⟩ := ha
          have mem_s := l_mem _ hb
          have x_diag := this ⟨_, mem_s⟩
          exact x_diag

      obtain ⟨z, l_prod_eq_diag⟩ := list_prod_trivial
      have x_neq := hx z
      rw [← l_prod_eq_diag] at x_neq
      rw [← l_prod_eq] at x_neq
      dsimp [List.unattach] at x_neq
      simp at x_neq

    obtain ⟨h, h_nontrivial⟩ := nontrivial_h

    have S_mem_G': ∀ s ∈ S, s ∈ (G' n (H_n_eps hn) G) := by
      rw [← S_generates]
      apply Subgroup.mem_closure_of_mem

    let s_to_map: S_finite.toFinset → (Subgroup.map G.subtype (G' n (H_n_eps hn) G)) := (fun a => (⟨a.val.val, by (
        simp
        simp [G']
        apply Subgroup.mem_closure_of_mem
        simp
        simp only [Subtype.dist_eq, dist_eq_norm_sub]
        have a_prop := a.property
        rw [Set.Finite.mem_toFinset] at a_prop
        have a_dist := S_dist a a_prop
        exact a_dist
      )⟩))





    have poly_pos := S_poly_data.S_poly_const_pos

    have my_map: ∃ a: ℕ, a ≥ 1 ∧ ∀ r ≥ 1, #(Finset.image s_to_map S_finite.toFinset.attach ^ r) ≤  a * r ^ (S_poly_data.S_poly_deg) := by
      have new_try := poly_growth_equiv S_poly_data.S_poly_const S_poly_data.S_poly_deg (by omega) (S_poly_data.S_finite.toFinset)
        (Finset.image (fun a => ⟨⟨(s_to_map a).val, by (apply SetLike.coe_mem)⟩, by (
          have foo := (s_to_map a).property
          rw [Subgroup.mem_map] at foo
          obtain ⟨x, x_mem, x_eq⟩ := foo
          simp_rw [← x_eq]
          simp [x_mem]
        )⟩) S_finite.toFinset.attach) ?_ ?_ ?_ ?_
      .
        obtain ⟨b, b_pos, hb⟩ := new_try
        use b
        refine ⟨b_pos, ?_⟩
        intro r hr
        rw [← Finset.card_image_of_injective (f := Subgroup.subtype _) _ (by apply subtype_injective)]
        rw [Finset.image_pow]
        rw [Finset.image_image]
        simp
        conv =>
          arg 1
          arg 1
          arg 1
          equals Finset.image (Subgroup.subtype _) S_finite.toFinset =>
            ext a
            rw [Finset.mem_image]
            refine ⟨?_, ?_⟩
            . intro x
              obtain ⟨y, y_mem, y_eq⟩ := x
              rw [Finset.mem_image]
              use y
              rw [← y_eq]
              simp [s_to_map]
            . intro x_mem
              rw [Finset.mem_image] at x_mem
              obtain ⟨y, y_mem, y_eq⟩ := x_mem
              use ⟨y, y_mem⟩
              simp [s_to_map]
              exact y_eq


        specialize hb r hr
        rw [← Finset.card_image_of_injective (f := Subgroup.subtype _) _ (by apply subtype_injective)] at hb
        rw [Finset.image_pow] at hb
        rw [← Finset.card_image_of_injective (f := Subgroup.subtype _) _ (by apply subtype_injective)] at hb
        rw [Finset.image_pow] at hb
        conv at hb =>
          arg 1
          arg 1
          arg 1
          equals Finset.image (Subgroup.subtype _) S_finite.toFinset =>
            ext a
            rw [Finset.mem_image]
            refine ⟨?_, ?_⟩
            . intro x
              obtain ⟨y, y_mem, y_eq⟩ := x
              rw [Finset.mem_image]
              use y
              rw [← y_eq]
              simp [s_to_map]
              rw [Finset.image_image] at y_mem
              rw [Finset.mem_image] at y_mem
              obtain ⟨z, z_mem, z_eq⟩ := y_mem
              simp at z_eq
              rw [← z_eq]
              simp [s_to_map]
              have z_prop := z.property
              rw [Set.Finite.mem_toFinset] at z_prop
              exact z_prop
            . intro x_mem
              rw [Finset.mem_image] at x_mem
              obtain ⟨y, y_mem, y_eq⟩ := x_mem
              use y
              refine ⟨?_, y_eq⟩
              rw [Finset.image_image]
              rw [Finset.mem_image]
              simp at y_mem
              use ⟨y, by simp [y_mem]⟩
              simp [s_to_map]
        exact hb
      .
        have fintype_s:  Fintype ↑S_poly_data.S := by
          refine Set.Finite.fintype ?_
          exact S_poly_data.S_finite


        simp
        conv =>
          rhs
          unfold Set.Finite.toFinset
          equals (S_poly_data.S).toFinset =>
            ext a
            simp
            nth_rw 1 [S_poly_data.S_inv]
            simp
      .
        simp
        apply S_poly_data.S_one
      .
        simp
        exact S_poly_data.S_generates
      .
        intro n hn
        have S_poly := S_poly_data.S_poly n hn
        exact S_poly


    obtain ⟨new_const, new_const_pos, h_poly_new_const⟩ := my_map


    let h_n_data: HnData := {
      d := n
      hd := hn
      G := Subgroup.map G.subtype (G' n (H_n_eps hn) G)
      G_central_trivial := by
        intro g hg
        apply G'_central_trivial ⟨⟨⟨g.val.val, by simp⟩, by (
          simp
          have prop := g.property
          rw [Subgroup.mem_map] at prop
          obtain ⟨q, q_mem, g_eq_q⟩ := prop
          rw [← g_eq_q]
          simp
        )⟩, by (
          simp
          have prop := g.property
          rw [Subgroup.mem_map] at prop
          obtain ⟨q, q_mem, g_eq_q⟩ := prop
          simp_rw [← g_eq_q]
          simp
          exact q_mem
        )⟩
        rw [← Subgroup.coe_center]
        rw [← Subgroup.coe_center] at hg
        simp
        simp at hg
        rw [Subgroup.mem_center_iff]
        rw [Subgroup.mem_center_iff] at hg
        intro a
        have foo := hg ⟨⟨a.val, by (
          simp
        )⟩, by(
          simp
        )⟩
        simp at foo
        simp [Subtype.ext_iff]
        rw [Subtype.ext_iff] at foo
        simp at foo
        rw [Subtype.ext_iff] at foo
        simpa using foo

      S := (((Finset.image s_to_map) S_finite.toFinset.attach : Finset _) : Set _)
      S_generates := by
        simp
        have orig_S'' := S''_generates
        apply_fun (Subgroup.map (G' n (H_n_eps hn) G).subtype) at S''_generates
        conv at S''_generates =>
          rhs
          equals (G' n (H_n_eps hn) G) =>
            ext a
            simp

        apply_fun (Subgroup.map ({
          toFun := fun a => (⟨a.val, (by
            have prop := a.property
            rw [Subgroup.mem_map] at prop
            obtain ⟨x, x_mem, x_eq⟩ := prop
            rw [← x_eq]
            simp
          )⟩ : G),
          map_one' := by
            simp
          map_mul' := by
            intro a b
            simp
        })) using (?_)
        . conv =>
            rhs
            equals (G' n (H_n_eps hn) G) =>
              ext a
              rw [Subgroup.mem_map]
              refine ⟨?_, ?_⟩
              .
                intro exists_x
                obtain ⟨x, x_mem, a_eq⟩ := exists_x
                simp at a_eq
                have x_prop := x.property
                rw [Subgroup.mem_map] at x_prop
                obtain ⟨y, y_mem, x_eq_y⟩ := x_prop
                rw [← a_eq]
                conv =>
                  arg 2
                  simp [← x_eq_y]
                exact y_mem
              . intro a_mem
                use ⟨a, ?_⟩
                . refine ⟨by simp, ?_⟩
                  simp
                . rw [Subgroup.mem_map]
                  use ⟨a, ?_⟩
                  . refine ⟨by simp; apply a_mem, ?_⟩
                    simp
                  . simp

          conv =>
            rhs
            rw [← S''_generates]
          ext a
          rw [Subgroup.mem_map]
          refine ⟨?_, ?_⟩
          .
            intro ha
            simp at ha
            simp
            obtain ⟨b, b_mem, a_mem_g, b_mem_closure, a_eq_b⟩ := ha
            use ?_
            . conv =>
                arg 2
                simp only [← a_eq_b]

              rw [orig_S'']
              simp
            . obtain ⟨b_mem, b_mem_g'⟩ := a_mem_g
              rw [← a_eq_b]
              simp [b_mem_g']
          . intro ha
            have a_val_mem: a.val ∈ Subgroup.map G.subtype (G' n (H_n_eps hn) G) := by
              simp at ha
              simp
              obtain ⟨a_mem_g', a_mem_closure⟩ := ha
              apply a_mem_g'

            use ⟨a, ?_⟩
            . refine ⟨?_, by simp⟩
              rw [←  Subgroup.mem_toSubmonoid]
              rw [Subgroup.closure_toSubmonoid]
              rw [← SetLike.mem_coe]
              rw [Submonoid.closure_eq_image_prod]
              rw [Set.mem_image]
              rw [Subgroup.mem_map] at ha
              obtain ⟨b, b_mem, a_eq_b⟩ := ha
              have b_prop := b.property
              conv at b_prop =>
                arg 1
                rw [← S_generates]
              have b_list := mem_closure_prod_list S S_eq_Sinv b b_prop
              obtain ⟨l, l_prod⟩ := b_list
              use List.map (fun d => ⟨d.val, ?_⟩) l
              .
                refine ⟨?_, ?_⟩
                .
                  rw [Set.mem_setOf (a := List.map _ _)]
                  intro p p_mem
                  apply Set.mem_union_left
                  rw [List.mem_map] at p_mem
                  rw [Set.mem_range]
                  obtain ⟨z, z_mem, z_eq_p⟩ := p_mem
                  use ⟨z, by simp⟩
                  rw [← z_eq_p]
                .
                  conv =>
                    rhs
                    simp [← a_eq_b]
                  conv =>
                    rhs
                    simp [← l_prod]
                  apply Subtype.ext
                  simp
                  rw [List.comp_map]
                  simp
                  apply congrArg
                  ext i g
                  simp

              .
                have my_mem := S_mem_G' d (by simp)
                apply Subgroup.mem_map_of_mem
                apply my_mem
            . exact a_val_mem

      S_finite := by
        simp
        apply Set.finite_range
      S_one := by
        simp
        dsimp [S]
        use 1
        use (by simp)
        use (by apply Subgroup.one_mem)
        use ?_
        simp [s_to_map]
        apply Set.mem_union_right
        simp
      S_inv := by
        intro s hs
        rw [Finset.mem_coe] at hs
        rw [Finset.mem_coe]
        rw [Finset.mem_image] at hs
        obtain ⟨x, x_mem, s_eq⟩ := hs
        rw [Finset.mem_image]
        use ⟨x⁻¹, ?_⟩
        .
          simp
          rw [← s_eq]
          rfl
        . simp

          nth_rw 1 [S_eq_Sinv]
          simp
          have x_prop := x.property
          rw [Set.Finite.mem_toFinset] at x_prop
          exact x_prop
      S_dist := by
        intro s hs
        rw [Finset.mem_coe] at hs
        rw [Finset.mem_image] at hs
        obtain ⟨x, x_mem, s_eq⟩ := hs
        have x_prop := x.property
        rw [Set.Finite.mem_toFinset] at x_prop
        have s_dist := S_dist x x_prop
        rw [← s_eq]
        linarith
      S_poly_const := new_const
      S_poly_const_pos := by
        omega
      S_poly_deg := S_poly_data.S_poly_deg
      S_poly := by
        simp
        apply h_poly_new_const
      h := ⟨⟨h.val.val, by (
        have h_prop := h.property
        simp only [S] at h_prop
        simp
        cases h_prop
        . rename_i h_mem
          . cases h_mem
            . rename_i h_prop
              dsimp [pre_S] at h_prop
              rw [Set.mem_iUnion] at h_prop
              obtain ⟨y, y_mem⟩ := h_prop
              simp [-Set.mem_inv] at y_mem
              have h_dist := S_dist h (by simp)
              simp [G']
              apply Subgroup.mem_closure_of_mem
              simp
              simp only [Subtype.dist_eq, dist_eq_norm_sub]
              exact h_dist
            . rename_i h_prop
              -- TODo: deduplicate
              dsimp [pre_S] at h_prop
              simp_rw [Set.iUnion_inv] at h_prop
              rw [Set.mem_iUnion] at h_prop
              obtain ⟨y, y_mem⟩ := h_prop
              simp [-Set.mem_inv] at y_mem
              have h_dist := S_dist h (by simp)
              simp [G']
              apply Subgroup.mem_closure_of_mem
              simp
              simp only [Subtype.dist_eq, dist_eq_norm_sub]
              exact h_dist
        . rename_i h_mem
          simp at h_mem
          simp [G']
          simp [h_mem]
      )⟩, by
        rw [Finset.mem_coe]
        rw [Finset.mem_image]
        use ⟨h.val, by simp⟩
        simp [s_to_map]
      ⟩
      h_nontrivial := by
        simpa using h_nontrivial
    }
    .
      apply Subgroup.map_injective
      simp
      intro x y hxy
      simpa using hxy

    have contra := H_n_contradiction h_n_data (1 / 50) ?_ ?_ ?_ ?_
    . contradiction
    . simp
    . simp
      norm_num
    .
      rw [← div_le_iff₀']
      .
        rw [le_inv_comm₀]
        .
          simp
          simp [H_n_eps]
          left
          norm_num
        . simp
        . apply H_n_eps_pos
      . simp
    .
      simp
      unfold H_n_eps

      simp
      right
      left
      rw [data_eq_degree]
      simp [h_n_data]
      norm_num
      apply div_lt_div₀
      . norm_num
      . apply le_refl
      . norm_num
      . positivity

end HnEpsData

-- TODO: upstream to mathlib


-- Helper for theorem 3.8
end

theorem solution : type_of% @HnEpsData.central_trivial_virtually_abelian_oai := @HnEpsData.central_trivial_virtually_abelian_oai
