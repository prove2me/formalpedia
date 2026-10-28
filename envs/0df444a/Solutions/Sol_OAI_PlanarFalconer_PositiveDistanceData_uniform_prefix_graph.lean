-- Prove2me | solution 1 for OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:52.524624+00:00
-- url     : https://prove2.me/submissions/047ba943-bbf5-4c6f-90b2-7c1e6012304d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_distance_equation12

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_MinimalDescriptorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_twice_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    a + 2*descriptorLength d ≤ t := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,ht,hw⟩ := Finset.mem_filter.mp hz
  have hu := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hl := originDescriptor_length A hq hu hw hd
  have hp := originDescriptor_length_le_anchor A hd
  omega

theorem policyDescriptor_length_le_half (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorLength d ≤ (t-a)/2 := by
  have := policyDescriptor_twice_length A hq hd
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixPolicyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem prefix_policy_geometry (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) :
    let p := policyDepth A N q a t
    a < p ∧ p ≤ t ∧ q ≤ p-a ∧ 2*(p-a) ≤ t-a ∧
      PolicyDescriptor.parallel a p ∈ policyDescriptorList A N q a t := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · change PolicyDescriptor.parallel a (policyDepth A N q a t) ∈ originDescriptors A N q a t
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_Ico.mpr ⟨?_,by omega⟩,rfl⟩
    have he : min (policyDepth A N q a t-a) (t-policyDepth A N q a t) =
        policyDepth A N q a t-a := min_eq_left (by omega)
    rw [he]
    omega

theorem prefix_policy_scales (A : ℕ → ℝ) {N q a t : ℕ}
    {sig kap v : ℝ} (hsig : 0 < sig) (hgap : 10*sig < kap)
    (hq : 0 < q) (hblock : kap*(N:ℝ) ≤ (q:ℝ))
    (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t)
    (hv : (t:ℝ)-sig*N ≤ v) (hvt : v ≤ t) :
    let p := policyDepth A N q a t
    let n := p-a
    a+n = p ∧ a+n ≤ N ∧ kap*N ≤ (n:ℝ) ∧
      10*sig*N ≤ v-(a+n) ∧ (n:ℝ) ≤ v-(a+n)+2*sig*N ∧
      ((t-a)/2:ℕ) ≤ v-(a+n)+2*sig*N ∧ v-a ≤ N := by
  have hg := prefix_policy_geometry A hq htN hw hpref
  let p := policyDepth A N q a t
  have hap : a ≤ p := hg.1.le
  have he : a+(p-a) = p := Nat.add_sub_of_le hap
  have hn : ((p-a:ℕ):ℝ) = (p:ℝ)-a := Nat.cast_sub hap
  have hpR : 2*(p:ℝ) ≤ (a:ℝ)+t := by exact_mod_cast hpref
  have hwR : (a:ℝ)+100*(q:ℝ) < (t:ℝ) := by exact_mod_cast hw
  have hqR : (q:ℝ) ≤ ((p-a:ℕ):ℝ) := by exact_mod_cast hg.2.2.1
  have htR : (t:ℝ) ≤ N := by exact_mod_cast htN
  have hsigN : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig.le (Nat.cast_nonneg _)
  have hgapN : 10*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right hgap.le (Nat.cast_nonneg _)
  have hhalf : 2*(((t-a)/2:ℕ):ℝ) ≤ (t:ℝ)-(a:ℝ) := by
    have hh : a+2*((t-a)/2) ≤ t := by omega
    have hhR : (a:ℝ)+2*(((t-a)/2:ℕ):ℝ) ≤ t := by exact_mod_cast hh
    linarith
  dsimp only
  refine ⟨he,by omega,hblock.trans hqR,?_,?_,?_,?_⟩
  · change 10*sig*N ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))
    rw [hn]
    nlinarith
  · change ((p-a:ℕ):ℝ) ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))+2*sig*N
    rw [hn]
    linarith
  · change (((t-a)/2:ℕ):ℝ) ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))+2*sig*N
    rw [hn]
    linarith
  · linarith [show (0:ℝ) ≤ (a:ℝ) from Nat.cast_nonneg a]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_PrefixGraphSpecialization
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PositiveDistanceData

theorem uniform_prefix_graph_oai {sig kap lam T eta : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heta : 0 < eta) (K : ℕ) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun n : ℕ => d.mass n-(n:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    ∀ v : ℝ, (d.t:ℝ)-sig*d.N ≤ v → v ≤ d.t →
    ∀ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.inverseDescriptorList, k l b ≤ K) →
    ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    d.policyParentEnergy k h v Ψ ≠ ⊤ ∧
    (d.policyParentEnergy k h v Ψ).toReal ≤
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta) *
      finiteEnergyMaximum (sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a))
        (d.policyCellEnergy d.inverseDescriptorList k h p v Ψ) + ((2:ℝ)^d.N)^(-T) := by
  classical
  obtain ⟨N₀,h₀⟩ := uniform_actual_distance_equation12 hsig hgap (by norm_num : (0:ℝ)<1)
    (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*Real.pi) K lam T hlam hT heta hJ hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref v hv hvt k hk h hh hhb
  have hg := prefix_policy_geometry A hq ht hw hpref
  have hsc := prefix_policy_scales A hsig hgap hq hblock ht hw hpref hv hvt
  have he : d.a+(p-d.a) = p := hsc.1
  have hprof' : RegularizedProfileData d.Q d.ρ d.N B δ lam d.mass := by
    simpa only [hdLam] using hprof
  have hcard (_index : Fin 2) : d.inverseDescriptorList.card ≤ (d.N+1)^3+1 :=
    (policyDescriptorList_card A hq).trans (Nat.le_succ _)
  have hL (_index : Fin 2) (b : PolicyDescriptor) (hb : b ∈ d.inverseDescriptorList) :
      descriptorLength b ≤ (d.t-d.a)/2 := policyDescriptor_length_le_half A hq hb
  have hdistinguished : PolicyDescriptor.parallel d.a (d.a+(p-d.a)) ∈ d.inverseDescriptorList := by
    rw [he]
    exact hg.2.2.2.2
  have ht' := h₀ d.N hN (fun _ : Fin 2 => d.inverseDescriptorList) (fun _ => id) k hcard hk
    ((d.t-d.a)/2) hL (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    B δ (fun _ => hprof') d.i h (by omega) hh hhb d.a (p-d.a) v
    hsc.2.1 hsc.2.2.1 hsc.2.2.2.1 hsc.2.2.2.2.1 hsc.2.2.2.2.2.1 hsc.2.2.2.2.2.2
    (fun _ => .parallel d.a (d.a+(p-d.a))) (fun _ => hdistinguished) (fun _ => rfl)
    d.X d.Y hX hY hlo hsep
  dsimp only at ht'
  rw [← hdLam,← hdSig,← hdJ] at ht'
  have heR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast he
  simp only [he,heR,min_self] at ht'
  have hexp : -(d.mass p-(p:ℝ)/d.N-(d.mass d.a-(d.a:ℝ)/d.N))
      -(d.mass p-(p:ℝ)/d.N-(d.mass d.a-(d.a:ℝ)/d.N))+
      height A d.a p+4000*(d.lam+d.sig)+eta =
      -2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta := by
    dsimp [A]
    rw [hdLam,hdSig]
    ring
  rw [hexp] at ht'
  exact ht'

end PositiveDistanceData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_graph_oai := @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_graph_oai
