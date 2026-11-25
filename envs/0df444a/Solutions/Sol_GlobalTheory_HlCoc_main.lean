-- Prove2me | solution 1 for GlobalTheory.HlCoc.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:10.250211+00:00
-- url     : https://prove2.me/submissions/5a50f5b5-ad22-45f5-a05d-909ee85d3fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
import Theorems.Thm_GlobalTheory_HlCoc_sndHom_apply
import Theorems.Thm_GlobalTheory_HlCoc_pow_fst_of_fixed
import Theorems.Thm_GlobalTheory_HlCoc_exists_pow_mul_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HlCoc.sndHom_apply
section
namespace GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
variable [TopologicalSpace G] [TopologicalSpace M]
variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]
private lemma exists_preimage_of_compact_hits_naturals (l : ℕ) [Fact l.Prime] {X : Type} [TopologicalSpace X] (S : Set X)
    (hS : IsCompact S) (f : X → Multiplicative ℤ_[l]) (hf : Continuous f)
    (hn : ∀ n : ℕ, ∃ x ∈ S, f x = Multiplicative.ofAdd (n : ℤ_[l]))
    (a : Multiplicative ℤ_[l]) : ∃ x ∈ S, f x = a := by
  have hcl : IsClosed (Multiplicative.ofAdd ⁻¹' (f '' S)) :=
    (hS.image hf).isClosed.preimage continuous_ofAdd
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[l]) ⊆ Multiplicative.ofAdd ⁻¹' (f '' S) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨x, hx, hfx⟩ := hn n
    exact ⟨x, hx, hfx⟩
  have hall := closure_minimal hsub hcl
  rw [PadicInt.denseRange_natCast.closure_range] at hall
  obtain ⟨x, hx, hfx⟩ := hall (Set.mem_univ (Multiplicative.toAdd a))
  exact ⟨x, hx, hfx⟩
private lemma cocycle_eq_of_agree_kernel_and_generator (l : ℕ) [Fact l.Prime] [CompactSpace G] [T2Space M]
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (hg₀ : lam g₀ = Multiplicative.ofAdd 1) (c₁ c₂ : G → M)
    (h₁ : Continuous c₁) (h₂ : Continuous c₂)
    (co₁ : ∀ g h, c₁ (g * h) = c₁ g + g • c₁ h) (co₂ : ∀ g h, c₂ (g * h) = c₂ g + g • c₂ h)
    (hH : ∀ h, lam h = 1 → c₁ h = c₂ h) (hg : c₁ g₀ = c₂ g₀) : c₁ = c₂ := by
  have h1 : c₁ 1 = c₂ 1 := hH 1 (map_one lam)
  let Z : Subgroup G :=
    { carrier := {g | c₁ g = c₂ g}
      mul_mem' := fun {x y} hx hy => by
        have hx' : c₁ x = c₂ x := hx
        have hy' : c₁ y = c₂ y := hy
        show c₁ (x * y) = c₂ (x * y)
        rw [co₁, co₂, hx', hy']
      one_mem' := h1
      inv_mem' := fun {x} hx => by
        have hx' : c₁ x = c₂ x := hx
        show c₁ x⁻¹ = c₂ x⁻¹
        have e1 := co₁ x⁻¹ x
        have e2 := co₂ x⁻¹ x
        rw [inv_mul_cancel] at e1 e2
        rw [hx'] at e1
        exact add_right_cancel (e1.symm.trans (h1.trans e2)) }
  have hZc : IsClosed (Z : Set G) := isClosed_eq h₁ h₂
  have hg₀Z : g₀ ∈ Z := hg
  funext g
  obtain ⟨k, hk, hkl⟩ := exists_preimage_of_compact_hits_naturals l (Z : Set G) hZc.isCompact lam hlam
    (fun n => ⟨g₀ ^ n, Z.pow_mem hg₀Z n, by rw [map_pow, hg₀, ← ofAdd_nsmul, nsmul_one]⟩) (lam g)
  have hk' : k⁻¹ * g ∈ Z := hH _ (by rw [map_mul, map_inv, hkl, inv_mul_cancel])
  have := Z.mul_mem hk hk'
  rwa [mul_inv_cancel_left] at this
end GlobalTheory.HlCoc
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
variable [TopologicalSpace G] [TopologicalSpace M]
variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]
namespace GlobalTheory.HlCoc
theorem _root_.solution (l : ℕ) [Fact l.Prime] [CompactSpace G] [T2Space G] [T2Space M]
    (T : AddSubgroup M) (hT : IsCompact (T : Set M)) (hTs : ∀ g : G, ∀ t ∈ T, g • t ∈ T)
    (hTl : ∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U)
    (lam : G →* Multiplicative ℤ_[l]) (g₀ : G) (hlam : Continuous lam)
    (hg₀ : lam g₀ = Multiplicative.ofAdd 1) (b z : M)
    (hH : ∀ h, lam h = 1 → h • z = z ∧ h • b - b ∈ T) (hz : z - (g₀ • b - b) ∈ T) :
    ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + g • c h) ∧
      (∀ h, lam h = 1 → c h = -(h • b - b)) ∧
      ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b) := by
  classical
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨e, he1, he2⟩ : ∃ e : SD M G, e.1 = z ∧ e.2 = g₀ := ⟨SD.mk z g₀, rfl, rfl⟩
  have hsn : ∀ (p : SD M G) (n : ℕ), (p ^ n).2 = p.2 ^ n := fun p n => by
    simpa using map_pow (sndHom : SD M G →* G) p n

  let F : Subgroup (SD M G) :=
    { carrier := {p | ∀ h : G, lam h = 1 → h • p.1 = p.1}
      mul_mem' := fun {p q} hp hq => by
        intro h hh
        have hk : lam (p.2⁻¹ * h * p.2) = 1 := by simp [hh]
        have e1 : h • p.2 • q.1 = p.2 • q.1 := by
          calc h • p.2 • q.1 = (p.2 * (p.2⁻¹ * h * p.2)) • q.1 := by
                rw [smul_smul]; congr 1; group
            _ = p.2 • (p.2⁻¹ * h * p.2) • q.1 := mul_smul _ _ _
            _ = p.2 • q.1 := by rw [hq _ hk]
        rw [mul_fst, smul_add, hp h hh, e1]
      one_mem' := by intro h _; simp
      inv_mem' := fun {p} hp => by
        intro h hh
        have hk : lam (p.2 * h * p.2⁻¹) = 1 := by simp [hh]
        rw [inv_fst, smul_neg]
        congr 1
        calc h • p.2⁻¹ • p.1 = (p.2⁻¹ * (p.2 * h * p.2⁻¹)) • p.1 := by
              rw [smul_smul]; congr 1; group
          _ = p.2⁻¹ • (p.2 * h * p.2⁻¹) • p.1 := mul_smul _ _ _
          _ = p.2⁻¹ • p.1 := by rw [hp _ hk] }
  have hFcl : IsClosed (F : Set (SD M G)) := by
    have : (F : Set (SD M G)) = ⋂ h : G, ⋂ (_ : lam h = 1), {p : SD M G | h • p.1 = p.1} := by
      ext p; simp [F]
    rw [this]
    exact isClosed_iInter fun h => isClosed_iInter fun _ =>
      isClosed_eq (continuous_const.smul cont_fst) cont_fst

  let W : Subgroup (SD M G) :=
    { carrier := {p | p.1 - (p.2 • b - b) ∈ T}
      mul_mem' := fun {p q} hp hq => by
        have e1 : (p * q).1 - ((p * q).2 • b - b) =
            (p.1 - (p.2 • b - b)) + p.2 • (q.1 - (q.2 • b - b)) := by
          rw [mul_fst, mul_snd, smul_sub, smul_sub, mul_smul]; abel
        show (p * q).1 - ((p * q).2 • b - b) ∈ T
        rw [e1]
        exact add_mem hp (hTs _ _ hq)
      one_mem' := by
        show (1 : SD M G).1 - ((1 : SD M G).2 • b - b) ∈ T
        simp
      inv_mem' := fun {p} hp => by
        have e1 : (p⁻¹).1 - ((p⁻¹).2 • b - b) = -(p.2⁻¹ • (p.1 - (p.2 • b - b))) := by
          rw [inv_fst, inv_snd, smul_sub, smul_sub, smul_smul, inv_mul_cancel, one_smul]; abel
        show (p⁻¹).1 - ((p⁻¹).2 • b - b) ∈ T
        rw [e1]
        exact neg_mem (hTs _ _ hp) }
  have hWc : IsCompact (W : Set (SD M G)) := by
    have hcont : Continuous (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G)) :=
      (continuous_fst.add ((continuous_snd.smul continuous_const).sub continuous_const)).prodMk
        continuous_snd
    have hEq : (W : Set (SD M G)) = (fun x : M × G => ((x.1 + (x.2 • b - b), x.2) : SD M G)) ''
        ((T : Set M) ×ˢ (Set.univ : Set G)) := by
      ext p
      constructor
      · intro hp
        refine ⟨(p.1 - (p.2 • b - b), p.2), ⟨hp, Set.mem_univ _⟩, ?_⟩
        show ((p.1 - (p.2 • b - b) + (p.2 • b - b), p.2) : M × G) = p
        rw [sub_add_cancel]
        rfl
      · rintro ⟨x, ⟨hx, -⟩, rfl⟩
        show x.1 + (x.2 • b - b) - (x.2 • b - b) ∈ T
        rw [add_sub_cancel_right]
        exact hx
    rw [hEq]
    exact (hT.prod (isCompact_univ : IsCompact (Set.univ : Set G))).image hcont

  let C : Subgroup (SD M G) := (Subgroup.zpowers e).topologicalClosure
  have heC : e ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers e)
  have hCF : (C : Set (SD M G)) ⊆ F :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by
      intro h hh
      show h • e.1 = e.1
      rw [he1]; exact (hH h hh).1)) hFcl
  have hCW : (C : Set (SD M G)) ⊆ W := by
    have hW : IsClosed (W : Set (SD M G)) := hWc.isClosed
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr (by
      show e.1 - (e.2 • b - b) ∈ T
      rw [he1, he2]; exact hz)) hW
  have hCc : IsCompact (C : Set (SD M G)) :=
    hWc.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) hCW
  have helam : lam e.2 = Multiplicative.ofAdd 1 := by rw [he2, hg₀]

  have key : ∀ q ∈ C, lam q.2 = 1 → q.1 = 0 := by
    intro q hq hq1
    have step : ∀ k : ℕ, ∃ r ∈ C, lam r.2 = 1 ∧ q = r ^ (l ^ k) := by
      intro k
      induction k with
      | zero => exact ⟨q, hq, hq1, by rw [pow_zero, pow_one]⟩
      | succ k ih =>
        obtain ⟨r, hr, hr1, hqr⟩ := ih
        obtain ⟨j, hj, s, hs, hrs⟩ := exists_pow_mul_pow e l hl hCc r hr
        have hlr : lam (e ^ j * s ^ l).2 = 1 := hrs ▸ hr1
        rw [mul_snd, hsn, hsn, map_mul, map_pow, map_pow, helam] at hlr
        have hadd : (j : ℤ_[l]) + l * Multiplicative.toAdd (lam s.2) = 0 := by
          have := congrArg Multiplicative.toAdd hlr
          simpa [toAdd_mul, toAdd_pow, nsmul_eq_mul] using this
        have hjz : (j : ZMod l) = 0 := by
          have := congrArg (PadicInt.toZMod (p := l)) hadd
          simpa using this
        have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff j l).mp hjz) hj
        rw [hj0, Nat.cast_zero, zero_add] at hadd
        have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
        have hy : Multiplicative.toAdd (lam s.2) = 0 := (mul_eq_zero.mp hadd).resolve_left hl0
        refine ⟨s, hs, Multiplicative.toAdd.injective (by rw [hy]; rfl), ?_⟩
        rw [hqr, hrs, hj0, pow_zero, one_mul, ← pow_mul, pow_succ']
    by_contra hne
    obtain ⟨k, hk⟩ := hTl ({q.1}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    obtain ⟨r, hr, hr1, hqr⟩ := step k
    have hfix : r.2 • r.1 = r.1 := hCF hr r.2 hr1
    have hrT : r.1 ∈ T := by
      have h1 : r.1 - (r.2 • b - b) ∈ T := hCW hr
      have h2 := add_mem h1 (hH r.2 hr1).2
      rwa [sub_add_cancel] at h2
    apply hk r.1 hrT
    rw [hqr, pow_fst_of_fixed r hfix]
    exact Set.mem_singleton _

  choose qq hqC hqlam using exists_preimage_of_compact_hits_naturals l (C : Set (SD M G)) hCc (fun q => lam q.2)
    (hlam.comp cont_snd) (fun n => ⟨e ^ n, C.pow_mem heC n, by
      show lam (e ^ n).2 = _
      rw [hsn, map_pow, helam, ← ofAdd_nsmul, nsmul_one]⟩)

  have hd : ∀ q ∈ C, (qq (lam q.2)).1 = q.1 := by
    intro q hq
    have hm : (qq (lam q.2))⁻¹ * q ∈ C := C.mul_mem (C.inv_mem (hqC _)) hq
    have h1 : lam ((qq (lam q.2))⁻¹ * q).2 = 1 := by
      rw [mul_snd, inv_snd, map_mul, map_inv, hqlam, inv_mul_cancel]
    have h0 := key _ hm h1
    calc (qq (lam q.2)).1
        = (qq (lam q.2)).1 + (qq (lam q.2)).2 • ((qq (lam q.2))⁻¹ * q).1 := by
          rw [h0, smul_zero, add_zero]
      _ = (qq (lam q.2) * ((qq (lam q.2))⁻¹ * q)).1 := (mul_fst _ _).symm
      _ = q.1 := by rw [mul_inv_cancel_left]
  have hdc : Continuous (fun a => (qq a).1) := by
    rw [continuous_iff_isClosed]
    intro K hK
    have hcl : IsClosed ((fun q : SD M G => lam q.2) ''
        ((C : Set (SD M G)) ∩ (fun q : SD M G => q.1) ⁻¹' K)) :=
      ((hCc.inter_right (hK.preimage cont_fst)).image (hlam.comp cont_snd)).isClosed
    convert hcl using 1
    ext a
    constructor
    · intro ha
      exact ⟨qq a, ⟨hqC a, ha⟩, hqlam a⟩
    · rintro ⟨q, ⟨hq, hqK⟩, rfl⟩
      show (qq (lam q.2)).1 ∈ K
      rw [hd q hq]; exact hqK
  obtain ⟨c, hcdef⟩ : ∃ c : G → M, ∀ g, c g = (qq (lam g)).1 - (g • b - b) :=
    ⟨_, fun _ => rfl⟩
  have cc : Continuous c := by
    rw [show c = fun g => (qq (lam g)).1 - (g • b - b) from funext hcdef]
    exact (hdc.comp hlam).sub ((continuous_id.smul continuous_const).sub continuous_const)
  have cT : ∀ g, c g ∈ T := by
    intro g
    have hq : (qq (lam g)).1 - ((qq (lam g)).2 • b - b) ∈ T := hCW (hqC (lam g))
    have hk : lam ((qq (lam g)).2⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hqlam, inv_mul_cancel]
    have hT2 := hTs (qq (lam g)).2 _ (hH _ hk).2
    have e1 : (qq (lam g)).1 - (g • b - b) = ((qq (lam g)).1 - ((qq (lam g)).2 • b - b)) -
        (qq (lam g)).2 • (((qq (lam g)).2⁻¹ * g) • b - b) := by
      rw [smul_sub, smul_smul, mul_inv_cancel_left]; abel
    rw [hcdef, e1]
    exact sub_mem hq hT2
  have cco : ∀ g h, c (g * h) = c g + g • c h := by
    intro g h
    have hm := C.mul_mem (hqC (lam g)) (hqC (lam h))
    have hl2 : lam (qq (lam g) * qq (lam h)).2 = lam (g * h) := by
      rw [mul_snd, map_mul, hqlam, hqlam, map_mul]
    have h1 := hd _ hm
    rw [hl2, mul_fst] at h1
    have hk : lam ((qq (lam g)).2⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hqlam, inv_mul_cancel]
    have hfx : g • (qq (lam h)).1 = (qq (lam g)).2 • (qq (lam h)).1 := by
      conv_lhs => rw [← mul_inv_cancel_left (qq (lam g)).2 g]
      rw [mul_smul, hCF (hqC (lam h)) _ hk]
    rw [hcdef, hcdef, hcdef, h1, smul_sub, smul_sub, hfx, mul_smul]; abel
  have cH : ∀ h, lam h = 1 → c h = -(h • b - b) := by
    intro h hh
    have h0 := hd 1 C.one_mem
    rw [one_snd, map_one, one_fst] at h0
    rw [hcdef, hh, h0, zero_sub]
  have cg : ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (g • b - b) := by
    intro g hg
    have h0 := hd e heC
    rw [helam, he1] at h0
    rw [hcdef, hg, h0]
  refine ⟨c, ⟨cc, cT, cco, cH, cg⟩, ?_⟩
  rintro c₂ ⟨hc₂, -, hco₂, hH₂, hg₂⟩
  exact cocycle_eq_of_agree_kernel_and_generator l lam hlam g₀ hg₀ c₂ c hc₂ cc hco₂ cco
    (fun h hh => by rw [hH₂ h hh, cH h hh]) (by rw [hg₂ g₀ hg₀, cg g₀ hg₀])
end GlobalTheory.HlCoc
