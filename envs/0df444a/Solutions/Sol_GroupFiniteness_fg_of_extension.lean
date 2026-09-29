-- Prove2me | solution 1 for GroupFiniteness.fg_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T09:00:31.992479+00:00
-- url     : https://prove2.me/submissions/8dfa5bad-2f56-40c1-b8e6-3921c9c0ade7

import Definitions.Def_MilnorWolf_Growth
import Mathlib

/-!
# Polycyclic groups (Wolf, Proposition 4.1 (1), p. 433)

Basic closure properties of `MilnorWolf.IsPolycyclic`: trivial groups and cyclic groups are
polycyclic, the notion is invariant under isomorphism, finitely generated abelian groups are
polycyclic, and an extension of a polycyclic group by a polycyclic group is polycyclic
(Rosenblatt's Remark 4.3).  Polycyclic groups are finitely generated and finitely presented.

The `Fin (t + 1)`-indexed normal series of the published definition is replaced, for the duration
of the proofs, by the `ℕ`-indexed characterisation `MilnorWolf.Lib.IsPolyChain`: a chain
`A : ℕ → Subgroup G` with `A 0 = ⊤`, eventually `⊥`, and each step normal with cyclic quotient.
-/

universe u v

namespace MilnorWolf
namespace Lib

open Function Subgroup

/-! ### One step of a normal series -/

/-- One step `H ⊆ K` of a normal series: `H ≤ K`, `H` is normal in `K`, and `K/H` is cyclic. -/
def IsCyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∃ _ : (H.subgroupOf K).Normal, IsCyclic (K ⧸ H.subgroupOf K)

/-- Transport of "normal with cyclic quotient" along a surjection, by pulling the subgroup back. -/
theorem normal_isCyclic_comap {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hφ : Surjective φ) {Q : Subgroup B} (hn : Q.Normal) (hc : IsCyclic (B ⧸ Q)) :
    ∃ _ : (Q.comap φ).Normal, IsCyclic (A ⧸ Q.comap φ) := by
  have : Q.Normal := hn
  have hn' : (Q.comap φ).Normal := hn.comap φ
  refine ⟨hn', ?_⟩
  have hker : Q.comap φ = ((QuotientGroup.mk' Q).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hs : Surjective ((QuotientGroup.mk' Q).comp φ) :=
    (QuotientGroup.mk'_surjective Q).comp hφ
  have e : A ⧸ Q.comap φ ≃* B ⧸ Q :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hs)
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- The restriction of `f : G →* H` to the preimage of `K`. -/
def restrictComap {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    ↥(K.comap f) →* ↥K :=
  (f.comp (K.comap f).subtype).codRestrict K (fun x => Subgroup.mem_comap.mp x.2)

@[simp] theorem restrictComap_coe {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H)
    (x : ↥(K.comap f)) : ((restrictComap f K x : ↥K) : H) = f (x : G) := rfl

theorem restrictComap_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Surjective f) (K : Subgroup H) : Surjective (restrictComap f K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, by simpa using hy⟩, rfl⟩

/-- A step of a normal series pulls back along a surjection. -/
theorem IsCyclicStep.comap {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Surjective f)
    {K₂ K₁ : Subgroup H} (h : IsCyclicStep K₂ K₁) :
    IsCyclicStep (K₂.comap f) (K₁.comap f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.comap_mono hle, ?_⟩
  have hkey : (K₂.subgroupOf K₁).comap (restrictComap f K₁) =
      (K₂.comap f).subgroupOf (K₁.comap f) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have := normal_isCyclic_comap (restrictComap f K₁) (restrictComap_surjective hf K₁)
    hnorm hcyc
  rwa [hkey] at this

/-- A step of a normal series pushes forward along an injection. -/
theorem IsCyclicStep.map {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Injective f)
    {H₂ H₁ : Subgroup G} (h : IsCyclicStep H₂ H₁) :
    IsCyclicStep (H₂.map f) (H₁.map f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_⟩
  have hcoe : ∀ x : ↥(H₁.map f),
      f (((Subgroup.equivMapOfInjective H₁ f hf).symm x : ↥H₁) : G) = (x : H) := by
    intro x
    conv_rhs => rw [← MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective H₁ f hf) x]
    exact (Subgroup.coe_equivMapOfInjective_apply H₁ f hf _).symm
  have hkey : (H₂.subgroupOf H₁).comap
      ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁) =
      (H₂.map f).subgroupOf (H₁.map f) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [← hcoe x]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have := normal_isCyclic_comap
    ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁)
    (Subgroup.equivMapOfInjective H₁ f hf).symm.surjective hnorm hcyc
  rwa [hkey] at this

theorem IsCyclicStep.congr {G : Type*} [Group G] {H K H' K' : Subgroup G} (h : IsCyclicStep H K)
    (e₁ : H = H') (e₂ : K = K') : IsCyclicStep H' K' := e₁ ▸ e₂ ▸ h

/-- The trivial step `⊥ ⊆ ⊥`. -/
theorem isCyclicStep_of_eq_bot {G : Type*} [Group G] {H K : Subgroup G} (hH : H = ⊥)
    (hK : K = ⊥) : IsCyclicStep H K := by
  subst hH; subst hK
  have hn : ((⊥ : Subgroup G).subgroupOf ⊥).Normal := by
    rw [Subgroup.subgroupOf_bot_eq_top]; infer_instance
  exact ⟨le_rfl, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-- The step `⊥ ⊆ ⊤` of a cyclic group. -/
theorem isCyclicStep_bot_top {G : Type*} [Group G] [IsCyclic G] :
    IsCyclicStep (⊥ : Subgroup G) ⊤ := by
  have hn : ((⊥ : Subgroup G).subgroupOf ⊤).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  exact ⟨bot_le, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-! ### An `ℕ`-indexed characterisation of `IsPolycyclic` -/

/-- A normal series of `G` indexed by `ℕ`: `A 0 = ⊤`, some `A t = ⊥`, and every step
`A (i+1) ⊆ A i` is normal with cyclic quotient. -/
def IsPolyChain {G : Type*} [Group G] (A : ℕ → Subgroup G) : Prop :=
  A 0 = ⊤ ∧ (∃ t, A t = ⊥) ∧ ∀ i, IsCyclicStep (A (i + 1)) (A i)

theorem isPolycyclic_of_chain {G : Type*} [Group G] {A : ℕ → Subgroup G} (h : IsPolyChain A) :
    IsPolycyclic G := by
  obtain ⟨h0, ⟨t, ht⟩, hstep⟩ := h
  exact ⟨t, fun i => A i.val, h0, ht, fun i => hstep i.val⟩

theorem exists_chain_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    ∃ A : ℕ → Subgroup G, IsPolyChain A := by
  obtain ⟨t, A, h0, hlast, hstep⟩ := h
  have hbot : ∀ m, t ≤ m →
      A ⟨min m t, Nat.lt_succ_of_le (min_le_right m t)⟩ = ⊥ := by
    intro m hm
    rw [← hlast]
    exact congrArg A (Fin.ext (by simp [Fin.val_last]; omega))
  refine ⟨fun n => A ⟨min n t, Nat.lt_succ_of_le (min_le_right n t)⟩, ?_, ⟨t, ?_⟩, ?_⟩
  · rw [← h0]; exact congrArg A (Fin.ext (by simp))
  · exact hbot t le_rfl
  · intro i
    rcases lt_or_ge i t with hi | hi
    · refine IsCyclicStep.congr (hstep ⟨i, hi⟩) (congrArg A (Fin.ext ?_))
        (congrArg A (Fin.ext ?_))
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]; omega
    · exact isCyclicStep_of_eq_bot (hbot (i + 1) (by omega)) (hbot i hi)

theorem isPolycyclic_iff_exists_chain {G : Type*} [Group G] :
    IsPolycyclic G ↔ ∃ A : ℕ → Subgroup G, IsPolyChain A :=
  ⟨exists_chain_of_isPolycyclic, fun ⟨_, h⟩ => isPolycyclic_of_chain h⟩

/-! ### The basic examples -/

/-- A trivial group is polycyclic. -/
theorem isPolycyclic_of_subsingleton {G : Type*} [Group G] [Subsingleton G] :
    IsPolycyclic G := by
  have hbot : (⊥ : Subgroup G) = ⊤ := by
    ext x
    simp [Subsingleton.elim x 1]
  exact isPolycyclic_of_chain (A := fun _ => ⊥)
    ⟨hbot, ⟨0, rfl⟩, fun _ => isCyclicStep_of_eq_bot rfl rfl⟩

/-- Being polycyclic is invariant under isomorphism. -/
theorem isPolycyclic_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsPolycyclic G) : IsPolycyclic H := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  refine isPolycyclic_of_chain (A := fun n => (A n).map (e : G →* H)) ⟨?_, ⟨t, ?_⟩, ?_⟩
  · show (A 0).map (e : G →* H) = ⊤
    rw [h0]; exact Subgroup.map_top_of_surjective _ e.surjective
  · show (A t).map (e : G →* H) = ⊥
    rw [ht]; exact Subgroup.map_bot _
  · exact fun i => (hstep i).map (EquivLike.injective e)

/-- A cyclic group is polycyclic. -/
theorem isPolycyclic_of_isCyclic {G : Type*} [Group G] [IsCyclic G] : IsPolycyclic G := by
  refine isPolycyclic_of_chain (A := fun n => if n = 0 then ⊤ else ⊥) ⟨rfl, ⟨1, rfl⟩, ?_⟩
  intro i
  match i with
  | 0 => exact isCyclicStep_bot_top
  | (j + 1) => exact isCyclicStep_of_eq_bot rfl rfl

/-! ### Extensions -/

/-- Rosenblatt's Remark 4.3: an extension of a polycyclic group by a polycyclic group is
polycyclic. -/
theorem isPolycyclic_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  obtain ⟨C, hC0, ⟨a, hCa⟩, hCstep⟩ := exists_chain_of_isPolycyclic hN
  obtain ⟨B, hB0, ⟨b0, hBb0⟩, hBstep⟩ := exists_chain_of_isPolycyclic hQ
  obtain ⟨b, hb1, hBb⟩ : ∃ b, 1 ≤ b ∧ B b = ⊥ :=
    ⟨b0 + 1, by omega, le_bot_iff.mp (by rw [← hBb0]; exact (hBstep b0).1)⟩
  have hmkN : (B b).comap (QuotientGroup.mk' N) = N := by
    rw [hBb, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hsubN : (C 0).map N.subtype = N := by
    rw [hC0, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine isPolycyclic_of_chain
    (A := fun i => if i < b then (B i).comap (QuotientGroup.mk' N)
      else (C (i - b)).map N.subtype) ⟨?_, ⟨b + a, ?_⟩, ?_⟩
  · show (if (0 : ℕ) < b then (B 0).comap (QuotientGroup.mk' N)
      else (C (0 - b)).map N.subtype) = ⊤
    rw [if_pos (by omega : (0 : ℕ) < b), hB0, Subgroup.comap_top]
  · show (if b + a < b then (B (b + a)).comap (QuotientGroup.mk' N)
      else (C (b + a - b)).map N.subtype) = ⊥
    rw [if_neg (by omega), show b + a - b = a by omega, hCa, Subgroup.map_bot]
  · intro i
    show IsCyclicStep
      (if i + 1 < b then (B (i + 1)).comap (QuotientGroup.mk' N)
        else (C (i + 1 - b)).map N.subtype)
      (if i < b then (B i).comap (QuotientGroup.mk' N) else (C (i - b)).map N.subtype)
    rcases lt_or_ge (i + 1) b with h1 | h1
    · rw [if_pos h1, if_pos (by omega : i < b)]
      exact (hBstep i).comap (QuotientGroup.mk'_surjective N)
    · rcases lt_or_ge i b with hi | hi
      · have hib : i + 1 = b := by omega
        rw [if_neg (by omega), if_pos hi, show i + 1 - b = 0 by omega]
        refine IsCyclicStep.congr ((hBstep i).comap (QuotientGroup.mk'_surjective N)) ?_ rfl
        rw [hib, hmkN, hsubN]
      · rw [if_neg (by omega), if_neg (by omega), show i + 1 - b = (i - b) + 1 by omega]
        exact (hCstep (i - b)).map (Subgroup.subtype_injective N)

/-! ### Finitely generated abelian groups -/

theorem isPolycyclic_of_top_eq_bot {G : Type*} [Group G] (h : (⊤ : Subgroup G) = ⊥) :
    IsPolycyclic G := by
  have : Subsingleton G := ⟨fun x y => by
    have hx : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]⟩
  exact isPolycyclic_of_subsingleton

/-- Induction on the size of a generating family: an abelian group generated by `n` elements is
polycyclic. -/
theorem isPolycyclic_commGroup_aux (n : ℕ) : ∀ (G : Type u) [CommGroup G] (s : Fin n → G),
    Subgroup.closure (Set.range s) = ⊤ → IsPolycyclic G := by
  induction n with
  | zero =>
    intro G _ s hgen
    refine isPolycyclic_of_top_eq_bot ?_
    rw [← hgen, Set.range_eq_empty, Subgroup.closure_empty]
  | succ n ih =>
    intro G _ s hgen
    set s' : Fin n → G := fun i => s i.succ with hs'
    set N : Subgroup G := Subgroup.closure (Set.range s') with hNdef
    have hmem : ∀ i : Fin n, s' i ∈ N := fun i => Subgroup.subset_closure ⟨i, rfl⟩
    have hNpoly : IsPolycyclic N := by
      refine ih N (fun i => (⟨s' i, hmem i⟩ : ↥N)) ?_
      apply Subgroup.map_injective (Subgroup.subtype_injective N)
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have himg : (N.subtype : ↥N → G) ''
          Set.range (fun i => (⟨s' i, hmem i⟩ : ↥N)) = Set.range s' := by
        rw [← Set.range_comp]; rfl
      rw [himg, ← hNdef]
    have hgen' : Subgroup.closure ((QuotientGroup.mk' N) '' Set.range s) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
    have hsub : (QuotientGroup.mk' N) '' Set.range s ⊆
        (Subgroup.zpowers ((QuotientGroup.mk' N) (s 0)) : Set (G ⧸ N)) := by
      rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Subgroup.mem_zpowers _
      · have h1 : (QuotientGroup.mk' N) (s j.succ) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (hmem j)
        rw [h1]
        exact Subgroup.one_mem _
    have hle : (⊤ : Subgroup (G ⧸ N)) ≤ Subgroup.zpowers ((QuotientGroup.mk' N) (s 0)) := by
      rw [← hgen']
      exact (Subgroup.closure_le _).2 hsub
    have hcyc : IsCyclic (G ⧸ N) :=
      ⟨⟨(QuotientGroup.mk' N) (s 0), fun x => hle (Subgroup.mem_top x)⟩⟩
    exact isPolycyclic_of_extension N hNpoly isPolycyclic_of_isCyclic

/-- A finitely generated abelian group is polycyclic. -/
theorem isPolycyclic_of_commGroup_of_fg {G : Type*} [CommGroup G] [Group.FG G] :
    IsPolycyclic G := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp ‹Group.FG G›
  have hrange : Set.range (fun i : Fin S.card => ((S.equivFin.symm i : {x // x ∈ S}) : G))
      = (S : Set G) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hy
      exact ⟨S.equivFin ⟨y, hy⟩, by simp⟩
  exact isPolycyclic_commGroup_aux S.card G _ (by rw [hrange]; exact hS)

/-! ### Polycyclic groups are finitely generated -/

theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : Group.FG A) :
    Group.FG B := by
  have := h
  exact Group.fg_of_surjective (f := (e : A →* B)) (fun b => ⟨e.symm b, by simp⟩)

theorem fg_of_isCyclic {C : Type*} [Group C] [IsCyclic C] : Group.FG C := by
  obtain ⟨g, hg⟩ := ‹IsCyclic C›.exists_generator
  refine Group.fg_iff.mpr ⟨{g}, ?_, Set.finite_singleton g⟩
  rw [← Subgroup.zpowers_eq_closure]
  exact eq_top_iff.2 fun x _ => hg x

/-- `Group.FG` is closed under extensions. -/
theorem fg_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Group.FG N) (hQ : Group.FG (G ⧸ N)) : Group.FG G := by
  obtain ⟨S, hS⟩ := (Group.fg_iff_subgroup_fg N).mp hN
  obtain ⟨T0, hT0, hT0fin⟩ := Group.fg_iff.mp hQ
  set T : Set G := (Function.surjInv (QuotientGroup.mk'_surjective N)) '' T0 with hTdef
  have hTfin : T.Finite := hT0fin.image _
  have hTimg : (QuotientGroup.mk' N) '' T = T0 := by
    rw [hTdef, ← Set.image_comp]
    refine Set.image_congr ?_ |>.trans (Set.image_id _)
    intro x _
    exact Function.surjInv_eq (QuotientGroup.mk'_surjective N) x
  have hNle : N ≤ Subgroup.closure ((S : Set G) ∪ T) := by
    rw [← hS]; exact Subgroup.closure_mono Set.subset_union_left
  have hTle : Subgroup.closure T ≤ Subgroup.closure ((S : Set G) ∪ T) :=
    Subgroup.closure_mono Set.subset_union_right
  refine Group.fg_iff.mpr ⟨(S : Set G) ∪ T, ?_, (S.finite_toSet).union hTfin⟩
  rw [eq_top_iff]
  intro x _
  have hx : (QuotientGroup.mk' N) x ∈ (Subgroup.closure T).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.map_closure, hTimg, hT0]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hxy⟩ := hx
  have hmem : y⁻¹ * x ∈ N := QuotientGroup.eq.mp hxy
  have hfac : x = y * (y⁻¹ * x) := by group
  rw [hfac]
  exact Subgroup.mul_mem _ (hTle hy) (hNle hmem)

/-- A polycyclic group is finitely generated. -/
theorem fg_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) : Group.FG G := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  have key : ∀ j : ℕ, Group.FG ↥(A (t - j)) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero, ht]
      exact (Group.fg_iff_subgroup_fg _).mpr Subgroup.FG.bot
    | succ j ihj =>
      rcases le_or_gt t j with hj | hj
      · have hjj : t - (j + 1) = t - j := by omega
        rw [hjj]; exact ihj
      · have he : t - j = (t - (j + 1)) + 1 := by omega
        rw [he] at ihj
        set i := t - (j + 1) with hi
        obtain ⟨hle, hnorm, hcyc⟩ := hstep i
        have hFGP : Group.FG ↥((A (i + 1)).subgroupOf (A i)) :=
          fg_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm ihj
        have hn := hnorm
        have hc := hcyc
        have hFGQ : Group.FG (↥(A i) ⧸ (A (i + 1)).subgroupOf (A i)) := fg_of_isCyclic
        exact fg_of_extension ((A (i + 1)).subgroupOf (A i)) hFGP hFGQ
  have hfg0 : Group.FG ↥(A 0) := by simpa using key t
  rw [h0] at hfg0
  exact fg_of_mulEquiv Subgroup.topEquiv hfg0

/-! ### Polycyclic groups are finitely presented -/

/-- Freeness: any homomorphism out of a free group lifts along a surjection. -/
theorem exists_lift_of_surjective {α : Type*} {A B : Type*} [Group A] [Group B]
    {f : A →* B} (hf : Function.Surjective f) (g : FreeGroup α →* B) :
    ∃ θ : FreeGroup α →* A, f.comp θ = g := by
  refine ⟨FreeGroup.lift (fun a => Function.surjInv hf (g (FreeGroup.of a))), ?_⟩
  apply FreeGroup.ext_hom
  intro a
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  exact Function.surjInv_eq hf _

/-- Tietze / change of generators: the kernel of *any* surjection from a finite-rank free group
onto a finitely presented group is finitely normally generated. -/
theorem ker_isFinitelyNormallyGenerated {C : Type*} [Group C]
    [Group.IsFinitelyPresented C] {n : ℕ} (χ : FreeGroup (Fin n) →* C)
    (hχ : Function.Surjective χ) : χ.ker.IsFinitelyNormallyGenerated := by
  obtain ⟨m, ψ, hψ, R, hRfin, hR⟩ := ‹Group.IsFinitelyPresented C›.out
  obtain ⟨θ, hθ⟩ := exists_lift_of_surjective hψ χ
  obtain ⟨σ, hσ⟩ := exists_lift_of_surjective hχ ψ
  have hθapp : ∀ w, ψ (θ w) = χ w := fun w => DFunLike.congr_fun hθ w
  have hσapp : ∀ w, χ (σ w) = ψ w := fun w => DFunLike.congr_fun hσ w
  set S : Set (FreeGroup (Fin n)) :=
    σ '' R ∪ Set.range (fun i : Fin n => (FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i))) with hSdef
  refine ⟨S, (hRfin.image _).union (Set.finite_range _), ?_⟩
  set K : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure S with hKdef
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (⟨r, hr, rfl⟩ | ⟨i, rfl⟩)
    · have hrk : r ∈ ψ.ker := by rw [← hR]; exact Subgroup.subset_normalClosure hr
      show χ (σ r) = 1
      rw [hσapp]
      exact hrk
    · show χ ((FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i))) = 1
      rw [map_mul, map_inv, hσapp, hθapp, inv_mul_cancel]
  · have key : (QuotientGroup.mk' K).comp (σ.comp θ) = QuotientGroup.mk' K := by
      apply FreeGroup.ext_hom
      intro i
      have hmem : (FreeGroup.of i)⁻¹ * σ (θ (FreeGroup.of i)) ∈ K :=
        Subgroup.subset_normalClosure (Or.inr ⟨i, rfl⟩)
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [eq_comm, ← inv_mul_eq_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    intro w hw
    have hθw : θ w ∈ ψ.ker := by
      show ψ (θ w) = 1
      rw [hθapp]
      exact hw
    have hmapped : σ (θ w) ∈ K := by
      have h1 : σ (θ w) ∈ (Subgroup.normalClosure R).map σ := ⟨θ w, by rw [hR]; exact hθw, rfl⟩
      have h2 : σ (θ w) ∈ Subgroup.normalClosure (σ '' R) :=
        Subgroup.map_normalClosure_le R σ h1
      exact Subgroup.normalClosure_mono (fun x hx => Or.inl hx) h2
    have hcong : (QuotientGroup.mk' K) (σ (θ w)) = (QuotientGroup.mk' K) w :=
      DFunLike.congr_fun key w
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).2 hmapped] at hcong
    exact (QuotientGroup.eq_one_iff w).1 hcong.symm

theorem fg_of_isFinitelyPresented {A : Type*} [Group A] [h : Group.IsFinitelyPresented A] :
    Group.FG A := by
  obtain ⟨m, φ, hφ, _⟩ := h.out
  exact Group.fg_of_surjective hφ

theorem exists_freeGroup_fin_surjective {A : Type*} [Group A] [Group.FG A] :
    ∃ (m : ℕ) (φ : FreeGroup (Fin m) →* A), Function.Surjective φ := by
  obtain ⟨α, hα, φ₀, hφ₀⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp ‹Group.FG A›
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact ⟨m, φ₀.comp (FreeGroup.freeGroupCongr e).symm.toMonoidHom,
    hφ₀.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩

/-- A cyclic group is finitely presented. -/
theorem isFinitelyPresented_of_isCyclic {C : Type*} [Group C] [IsCyclic C] :
    Group.IsFinitelyPresented C := by
  obtain ⟨g, hg⟩ := ‹IsCyclic C›.exists_generator
  have hsurj : Function.Surjective (zpowersHom C g) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    exact ⟨Multiplicative.ofAdd m, by simpa using hm⟩
  refine Group.IsFinitelyPresented.of_surjective (zpowersHom C g) hsurj ?_
  have : Group.FG ↥(zpowersHom C g).ker := fg_of_isCyclic
  exact Subgroup.IsFinitelyNormallyGenerated.of_FG _

/-- P. Hall: an extension of a finitely presented group by a finitely presented group is
finitely presented. -/
theorem isFinitelyPresented_of_extension {G : Type*} [Group G] (N : Subgroup G)
    [hNnormal : N.Normal]
    (hN : Group.IsFinitelyPresented N) (hQ : Group.IsFinitelyPresented (G ⧸ N)) :
    Group.IsFinitelyPresented G := by
  have hNfg : Group.FG N := fg_of_isFinitelyPresented
  have hQfg : Group.FG (G ⧸ N) := fg_of_isFinitelyPresented
  have hGfg : Group.FG G := fg_of_extension N hNfg hQfg
  obtain ⟨n, φ, hφ⟩ := exists_freeGroup_fin_surjective (A := G)
  refine ⟨n, φ, hφ, ?_⟩
  -- `M = φ⁻¹ N` is finitely normally generated in the free group
  have hχ : Function.Surjective ((QuotientGroup.mk' N).comp φ) :=
    (QuotientGroup.mk'_surjective N).comp hφ
  have hMker : ((QuotientGroup.mk' N).comp φ).ker = N.comap φ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  obtain ⟨R, hRfin, hR⟩ : (N.comap φ).IsFinitelyNormallyGenerated := by
    rw [← hMker]; exact ker_isFinitelyNormallyGenerated _ hχ
  -- a presentation of `N`, and lifts of its generators to the free group
  obtain ⟨k, ρ₀, hρ₀⟩ := exists_freeGroup_fin_surjective (A := (↥N))
  obtain ⟨S, hSfin, hS⟩ := ker_isFinitelyNormallyGenerated ρ₀ hρ₀
  set ρ : FreeGroup (Fin k) →* G := N.subtype.comp ρ₀ with hρdef
  have hρker : ρ.ker = ρ₀.ker := by
    rw [hρdef]
    ext x
    exact ⟨fun h => Subtype.ext h, fun h => by
      show ((ρ₀ x : ↥N) : G) = 1
      rw [h]; rfl⟩
  have hρrange : ρ.range = N := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact (ρ₀ z).2
    · intro y hy
      obtain ⟨z, hz⟩ := hρ₀ ⟨y, hy⟩
      exact ⟨z, by rw [hρdef]; simp [hz]⟩
  set μ : Fin k → FreeGroup (Fin n) := fun j => Function.surjInv hφ (ρ (FreeGroup.of j)) with hμdef
  have hμφ : ∀ j, φ (μ j) = ρ (FreeGroup.of j) := fun j => Function.surjInv_eq hφ _
  set lam : FreeGroup (Fin k) →* FreeGroup (Fin n) := FreeGroup.lift μ with hlamdef
  have hlamof : ∀ j, lam (FreeGroup.of j) = μ j := by
    intro j; rw [hlamdef]; simp
  have hlam : ∀ z, φ (lam z) = ρ z := by
    have hcomp : φ.comp lam = ρ := by
      apply FreeGroup.ext_hom
      intro j
      simp only [MonoidHom.comp_apply, hlamof j, hμφ j]
    exact fun z => DFunLike.congr_fun hcomp z
  set Msub : Subgroup (FreeGroup (Fin n)) := Subgroup.closure (Set.range μ) with hMsubdef
  have hMsubmap : Msub.map φ = N := by
    have h1 : φ '' Set.range μ = ρ '' Set.range FreeGroup.of := by
      rw [← Set.range_comp, ← Set.range_comp]
      exact congrArg Set.range (funext hμφ)
    rw [hMsubdef, MonoidHom.map_closure, h1, ← MonoidHom.map_closure,
      FreeGroup.closure_range_of, ← MonoidHom.range_eq_map, hρrange]
  -- a choice of `Msub`-representative for every element whose image lies in `N`
  have hex : ∀ x : FreeGroup (Fin n), ∃ u : FreeGroup (Fin n),
      φ x ∈ N → (u ∈ Msub ∧ φ u = φ x) := by
    intro x
    by_cases hx : φ x ∈ N
    · rw [← hMsubmap] at hx
      obtain ⟨u, hu, hux⟩ := hx
      exact ⟨u, fun _ => ⟨hu, hux⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose c hc using hex
  have hμN : ∀ j, φ (μ j) ∈ N := by
    intro j
    rw [hμφ j, ← hρrange]
    exact ⟨FreeGroup.of j, rfl⟩
  have hconjN : ∀ (i : Fin n) (j : Fin k),
      φ (FreeGroup.of i * μ j * (FreeGroup.of i)⁻¹) ∈ N := by
    intro i j
    simp only [map_mul, map_inv]
    exact hNnormal.conj_mem _ (hμN j) _
  have hconjN' : ∀ (i : Fin n) (j : Fin k),
      φ ((FreeGroup.of i)⁻¹ * μ j * FreeGroup.of i) ∈ N := by
    intro i j
    simp only [map_mul, map_inv]
    exact hNnormal.conj_mem' _ (hμN j) _
  have hRsub : ∀ r ∈ R, φ r ∈ N := by
    intro r hr
    have hrm : r ∈ N.comap φ := by rw [← hR]; exact Subgroup.subset_normalClosure hr
    exact hrm
  -- the finite set of relations
  set T : Set (FreeGroup (Fin n)) :=
    ((fun x => x * (c x)⁻¹) '' R ∪
      Set.range (fun p : Fin n × Fin k =>
        (FreeGroup.of p.1 * μ p.2 * (FreeGroup.of p.1)⁻¹) *
          (c (FreeGroup.of p.1 * μ p.2 * (FreeGroup.of p.1)⁻¹))⁻¹) ∪
      Set.range (fun p : Fin n × Fin k =>
        ((FreeGroup.of p.1)⁻¹ * μ p.2 * FreeGroup.of p.1) *
          (c ((FreeGroup.of p.1)⁻¹ * μ p.2 * FreeGroup.of p.1))⁻¹)) ∪
      lam '' S with hTdef
  have hTfin : T.Finite :=
    (((hRfin.image _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (hSfin.image _)
  refine ⟨T, hTfin, ?_⟩
  set L : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure T with hLdef
  have hmemT : ∀ x ∈ T, x ∈ L := fun x hx => Subgroup.subset_normalClosure hx
  have hker_c : ∀ x, φ x ∈ N → x * (c x)⁻¹ ∈ φ.ker := by
    intro x hx
    simp [MonoidHom.mem_ker, (hc x hx).2]
  -- one inclusion: every relation lies in the kernel
  have hLK : L ≤ φ.ker := by
    rw [hLdef]
    apply Subgroup.normalClosure_le_normal
    rintro x (((⟨r, hr, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact hker_c r (hRsub r hr)
    · exact hker_c _ (hconjN i j)
    · exact hker_c _ (hconjN' i j)
    · have hsk : s ∈ ρ₀.ker := by rw [← hS]; exact Subgroup.subset_normalClosure hs
      show φ (lam s) = 1
      rw [hlam s, ← hρker] at *
      exact hsk
  refine le_antisymm hLK ?_
  -- the other inclusion
  set π : FreeGroup (Fin n) →* FreeGroup (Fin n) ⧸ L := QuotientGroup.mk' L with hπdef
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective L
  set P : Subgroup (FreeGroup (Fin n) ⧸ L) := Msub.map π with hPdef
  have hP_eq : P = Subgroup.closure (Set.range (fun j => π (μ j))) := by
    rw [hPdef, hMsubdef, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hpi_eq : ∀ x, x * (c x)⁻¹ ∈ L → π x = π (c x) := by
    intro x hx
    have h1 : π (x * (c x)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hx
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hcP : ∀ x, φ x ∈ N → π (c x) ∈ P := by
    intro x hx
    exact ⟨c x, (hc x hx).1, rfl⟩
  have hconjP : ∀ (i : Fin n) (j : Fin k),
      π (FreeGroup.of i) * π (μ j) * (π (FreeGroup.of i))⁻¹ ∈ P := by
    intro i j
    have hT : (FreeGroup.of i * μ j * (FreeGroup.of i)⁻¹) *
        (c (FreeGroup.of i * μ j * (FreeGroup.of i)⁻¹))⁻¹ ∈ T :=
      Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))
    have heq := hpi_eq _ (hmemT _ hT)
    rw [map_mul, map_mul, map_inv] at heq
    rw [heq]
    exact hcP _ (hconjN i j)
  have hconjP' : ∀ (i : Fin n) (j : Fin k),
      (π (FreeGroup.of i))⁻¹ * π (μ j) * π (FreeGroup.of i) ∈ P := by
    intro i j
    have hT : ((FreeGroup.of i)⁻¹ * μ j * FreeGroup.of i) *
        (c ((FreeGroup.of i)⁻¹ * μ j * FreeGroup.of i))⁻¹ ∈ T :=
      Or.inl (Or.inr ⟨(i, j), rfl⟩)
    have heq := hpi_eq _ (hmemT _ hT)
    rw [map_mul, map_mul, map_inv] at heq
    rw [heq]
    exact hcP _ (hconjN' i j)
  have hconj_into : ∀ g : FreeGroup (Fin n) ⧸ L,
      (∀ j, g * π (μ j) * g⁻¹ ∈ P) → ∀ h ∈ P, g * h * g⁻¹ ∈ P := by
    intro g hg h hh
    have hsub : Subgroup.closure (Set.range (fun j => π (μ j))) ≤
        P.comap ((MulAut.conj g : _ ≃* _) : _ →* _) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      simpa [MulAut.conj_apply] using hg j
    have := hsub (hP_eq.le hh)
    simpa [MulAut.conj_apply] using this
  have hnormalizer : ∀ i : Fin n,
      π (FreeGroup.of i) ∈ Subgroup.normalizer (P : Set (FreeGroup (Fin n) ⧸ L)) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hconj_into _ (fun j => hconjP i j) h hh
    · intro hh
      have h2 := hconj_into (π (FreeGroup.of i))⁻¹
        (by intro j; rw [inv_inv]; exact hconjP' i j) _ hh
      have e : (π (FreeGroup.of i))⁻¹ * (π (FreeGroup.of i) * h * (π (FreeGroup.of i))⁻¹) *
          (π (FreeGroup.of i))⁻¹⁻¹ = h := by group
      rwa [e] at h2
  have hnormtop : Subgroup.normalizer (P : Set (FreeGroup (Fin n) ⧸ L)) = ⊤ := by
    have hc2 : (Subgroup.normalizer (P : Set (FreeGroup (Fin n) ⧸ L))).comap π = ⊤ := by
      rw [eq_top_iff, ← FreeGroup.closure_range_of (Fin n), Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hnormalizer i
    calc Subgroup.normalizer (P : Set (FreeGroup (Fin n) ⧸ L))
        = ((Subgroup.normalizer (P : Set (FreeGroup (Fin n) ⧸ L))).comap π).map π :=
          (Subgroup.map_comap_eq_self_of_surjective hπsurj _).symm
      _ = ⊤ := by rw [hc2]; exact Subgroup.map_top_of_surjective _ hπsurj
  have hPnormal : P.Normal := Subgroup.normalizer_eq_top_iff.mp hnormtop
  have hMle : (N.comap φ).map π ≤ P := by
    rw [← hR]
    refine le_trans (Subgroup.map_normalClosure_le R π) (Subgroup.normalClosure_le_normal ?_)
    rintro _ ⟨r, hr, rfl⟩
    have hT : r * (c r)⁻¹ ∈ T := Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩))
    have heq := hpi_eq _ (hmemT _ hT)
    rw [heq]
    exact hcP _ (hRsub r hr)
  have hPrange : P = (π.comp lam).range := by
    rw [hP_eq, MonoidHom.range_eq_map, ← FreeGroup.closure_range_of (Fin k),
      MonoidHom.map_closure, ← Set.range_comp]
    exact congrArg Subgroup.closure (congrArg Set.range (funext fun j => by
      simp [hlamof j]))
  intro w hw
  have hwM : w ∈ N.comap φ := by
    have : φ w = 1 := hw
    simp [Subgroup.mem_comap, this]
  have hwP : π w ∈ P := hMle ⟨w, hwM, rfl⟩
  rw [hPrange] at hwP
  obtain ⟨z, hz⟩ := hwP
  have hdiff : (lam z)⁻¹ * w ∈ L := QuotientGroup.eq.mp hz
  have hφd : φ ((lam z)⁻¹ * w) = 1 := hLK hdiff
  have hrz : ρ z = 1 := by
    rw [← hlam z]
    have hw1 : φ w = 1 := hw
    rw [map_mul, map_inv, hw1, mul_one, inv_eq_one] at hφd
    exact hφd
  have hzker : z ∈ Subgroup.normalClosure S := by
    rw [hS, ← hρker]
    exact hrz
  have hlamz : lam z ∈ L := by
    have h1 : lam z ∈ (Subgroup.normalClosure S).map lam := ⟨z, hzker, rfl⟩
    have h2 : lam z ∈ Subgroup.normalClosure (lam '' S) :=
      Subgroup.map_normalClosure_le S lam h1
    exact Subgroup.normalClosure_le_normal (fun x hx => hmemT x (Or.inr hx)) h2
  have hπw : π w = 1 := by
    rw [← hz]
    exact (QuotientGroup.eq_one_iff _).2 hlamz
  exact (QuotientGroup.eq_one_iff w).1 hπw

/-- A polycyclic group is finitely presented. -/
theorem isFinitelyPresented_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    Group.IsFinitelyPresented G := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  have key : ∀ j : ℕ, Group.IsFinitelyPresented ↥(A (t - j)) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero, ht]
      have : Finite ↥(⊥ : Subgroup G) := inferInstance
      infer_instance
    | succ j ihj =>
      rcases le_or_gt t j with hj | hj
      · have hjj : t - (j + 1) = t - j := by omega
        rw [hjj]; exact ihj
      · have he : t - j = (t - (j + 1)) + 1 := by omega
        rw [he] at ihj
        set i := t - (j + 1) with hi
        obtain ⟨hle, hnorm, hcyc⟩ := hstep i
        have hFPP : Group.IsFinitelyPresented ↥((A (i + 1)).subgroupOf (A i)) := by
          have := ihj
          exact Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hle).symm
        have hn := hnorm
        have hc := hcyc
        have hFPQ : Group.IsFinitelyPresented (↥(A i) ⧸ (A (i + 1)).subgroupOf (A i)) :=
          isFinitelyPresented_of_isCyclic
        exact isFinitelyPresented_of_extension ((A (i + 1)).subgroupOf (A i)) hFPP hFPQ
  have hfp0 : Group.IsFinitelyPresented ↥(A 0) := by
    have hkt := key t
    rwa [Nat.sub_self] at hkt
  rw [h0] at hfp0
  have := hfp0
  exact Group.IsFinitelyPresented.equiv Subgroup.topEquiv

end Lib
end MilnorWolf

theorem solution {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.FG N] [Group.FG (G ⧸ N)] : Group.FG G :=
  MilnorWolf.Lib.fg_of_extension N inferInstance inferInstance
