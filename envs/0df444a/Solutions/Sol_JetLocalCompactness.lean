-- Prove2me | solution 1 for JetLocalCompactness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:10.090629+00:00
-- url     : https://prove2.me/submissions/a2663644-08b4-49a1-a91a-9c41a168ffec

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetLocalCompactness

set_option autoImplicit false

theorem _root_.solution (W : Set Plane) (hW : IsOpen W) (J : ℕ → Plane → ℝ × Plane)
    (hunif : ∀ K : Set Plane, K ⊆ W → IsCompact K →
      ∃ (N : ℕ) (A : ℝ),
        (∀ n, N ≤ n → ContinuousOn (J n) K) ∧
        (∀ n, N ≤ n → ∀ z ∈ K, ‖J n z‖ ≤ A) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n, N ≤ n → ∀ z ∈ K, ∀ z' ∈ K,
          dist z z' < δ → dist (J n z) (J n z') ≤ ε)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Jlim : Plane → ℝ × Plane,
      ∀ K : Set Plane, K ⊆ W → IsCompact K →
        TendstoUniformlyOn (fun i => J (φ i)) Jlim Filter.atTop K := by
  classical
  -- A compact exhaustion of the open set `W`, via one of the open subtype.
  obtain ⟨Kx, hKxc, hKxsub, hKxmono, hKxsuper⟩ :
      ∃ Kx : ℕ → Set Plane, (∀ j, IsCompact (Kx j)) ∧ (∀ j, Kx j ⊆ W) ∧
        (∀ j j', j ≤ j' → Kx j ⊆ Kx j') ∧
        (∀ K : Set Plane, K ⊆ W → IsCompact K → ∃ j, K ⊆ Kx j) := by
    have h1 : LocallyCompactSpace (↥W) := hW.locallyCompactSpace
    have h2 : SigmaCompactSpace (↥W) := by infer_instance
    let E := CompactExhaustion.choice (↥W)
    refine ⟨fun j => Subtype.val '' (E j), fun j => ?_, fun j => ?_, fun j j' h => ?_, ?_⟩
    · exact Subtype.isCompact_iff.mp (E.isCompact j)
    · rintro z ⟨x, _, rfl⟩; exact x.2
    · exact Set.image_mono (E.subset h)
    · intro K hK hKc
      have hS : IsCompact {x : ↥W | (x : Plane) ∈ K} := by
        rw [Subtype.isCompact_iff]
        convert hKc using 1
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩; exact hx
        · intro hz; exact ⟨⟨z, hK hz⟩, hz, rfl⟩
      obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact hS
      exact ⟨j, fun z hz => ⟨⟨z, hK hz⟩, hj hz, rfl⟩⟩
  -- The sequential Arzela-Ascoli step on ONE compact set, kept private to this node:
  -- bundle into `K →ᵇ (ℝ × Plane)`, use Mathlib's `arzela_ascoli` to get compactness of the
  -- closure, extract a convergent subsequence, and unbundle.  Mathlib has no sequential form.
  have hop : ∀ (K : Set Plane), IsCompact K → ∀ (H : ℕ → Plane → ℝ × Plane) (A : ℝ),
      (∀ n, ContinuousOn (H n) K) → (∀ n, ∀ z ∈ K, ‖H n z‖ ≤ A) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ z ∈ K, ∀ z' ∈ K,
        dist z z' < δ → dist (H n z) (H n z') ≤ ε) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Hl : Plane → ℝ × Plane,
        TendstoUniformlyOn (fun i => H (σ i)) Hl Filter.atTop K := by
    intro K hKc H A hcont hbd hec
    have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    let f : ℕ → BoundedContinuousFunction (↥K) (ℝ × Plane) := fun n =>
      BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict (H n), (hcont n).domRestrict⟩
    have hfapp : ∀ n (x : ↥K), f n x = H n x.1 := fun n x => rfl
    have hball : IsCompact (Metric.closedBall (0 : ℝ × Plane) A) := isCompact_closedBall _ _
    have hin : ∀ (g : BoundedContinuousFunction (↥K) (ℝ × Plane)) (x : ↥K), g ∈ Set.range f →
        g x ∈ Metric.closedBall (0 : ℝ × Plane) A := by
      intro g x hg
      obtain ⟨n, rfl⟩ := hg
      simp only [Metric.mem_closedBall, dist_zero_right, hfapp]
      exact hbd n x.1 x.2
    have hequi : Equicontinuous ((fun g => (g : ↥K → ℝ × Plane)) :
        ↥(Set.range f) → ↥K → ℝ × Plane) := by
      refine UniformEquicontinuous.equicontinuous ?_
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hec (ε / 2) (by positivity)
      refine ⟨δ, hδ, ?_⟩
      intro x y hxy g
      obtain ⟨n, hn⟩ := g.2
      have hgx : (g : ↥K → ℝ × Plane) x = H n x.1 := by rw [← hn]; rfl
      have hgy : (g : ↥K → ℝ × Plane) y = H n y.1 := by rw [← hn]; rfl
      rw [hgx, hgy]
      have hxy' : dist x.1 y.1 < δ := by rwa [Subtype.dist_eq] at hxy
      exact lt_of_le_of_lt (hδ' n x.1 x.2 y.1 y.2 hxy') (by linarith)
    have hcompact : IsCompact (closure (Set.range f)) :=
      BoundedContinuousFunction.arzela_ascoli _ hball _ hin hequi
    obtain ⟨a, _, σ, hσ, hconv⟩ :=
      hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
    refine ⟨σ, hσ, fun z => if h : z ∈ K then a ⟨z, h⟩ else 0, ?_⟩
    rw [tendstoUniformlyOn_iff_restrict]
    have huni : TendstoUniformly (fun i => (f (σ i) : ↥K → ℝ × Plane))
        (a : ↥K → ℝ × Plane) Filter.atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
    convert huni using 2 with i
    · funext x; rfl
    · funext x; simp
  -- Step 1: extraction on one piece of the exhaustion, after an arbitrary earlier extraction.
  have claim : ∀ (j : ℕ) (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Plane → ℝ × Plane,
        TendstoUniformlyOn (fun i => J (σ (τ i))) L Filter.atTop (Kx j) := by
    intro j σ hσ
    obtain ⟨N, A, hc, hb, he⟩ := hunif (Kx j) (hKxsub j) (hKxc j)
    have hge : ∀ i : ℕ, N ≤ σ (N + i) := fun i =>
      le_trans (Nat.le_add_right N i) hσ.le_apply
    obtain ⟨ρ, hρ, L, hL⟩ := hop (Kx j) (hKxc j) (fun i => J (σ (N + i))) A
      (fun i => hc _ (hge i)) (fun i => hb _ (hge i))
      (fun ε hε => by
        obtain ⟨δ, hδ, hδ'⟩ := he ε hε
        exact ⟨δ, hδ, fun i => hδ' _ (hge i)⟩)
    exact ⟨fun i => N + ρ i, fun a b hab => Nat.add_lt_add_left (hρ hab) N, L, hL⟩
  choose τ hτ1 L hτ2 using claim
  -- Step 2: the nested extraction, with the witnesses named so Step 3 can use them.
  let Φ : ℕ → {σ : ℕ → ℕ // StrictMono σ} := fun j => Nat.rec
    (⟨τ 0 id strictMono_id, hτ1 0 id strictMono_id⟩)
    (fun j prev => ⟨prev.1 ∘ τ (j + 1) prev.1 prev.2,
      prev.2.comp (hτ1 (j + 1) prev.1 prev.2)⟩) j
  have hΦsucc : ∀ j, (Φ (j + 1)).1 = (Φ j).1 ∘ τ (j + 1) (Φ j).1 (Φ j).2 := fun j => rfl
  have hstage : ∀ j, ∃ Lj : Plane → ℝ × Plane,
      TendstoUniformlyOn (fun i => J ((Φ j).1 i)) Lj Filter.atTop (Kx j) := by
    intro j
    cases j with
    | zero => exact ⟨L 0 id strictMono_id, hτ2 0 id strictMono_id⟩
    | succ j => exact ⟨L (j + 1) (Φ j).1 (Φ j).2, hτ2 (j + 1) (Φ j).1 (Φ j).2⟩
  -- Every later stage reindexes an earlier one by a map that dominates the identity.
  have hfact : ∀ j j', j ≤ j' → ∃ θ : ℕ → ℕ, (∀ m, m ≤ θ m) ∧
      ∀ m, (Φ j').1 m = (Φ j).1 (θ m) := by
    intro j j' hjj'
    induction j', hjj' using Nat.le_induction with
    | base => exact ⟨id, fun m => le_rfl, fun m => rfl⟩
    | succ j' hj' ih =>
      obtain ⟨θ, hθ, hθeq⟩ := ih
      refine ⟨θ ∘ τ (j' + 1) (Φ j').1 (Φ j').2, fun m => ?_, fun m => ?_⟩
      · exact le_trans (hτ1 (j' + 1) (Φ j').1 (Φ j').2).le_apply (hθ _)
      · rw [hΦsucc j']
        exact hθeq _
  -- Step 3: the diagonal subsequence, and the limit as a pointwise `limUnder`.
  refine ⟨fun i => (Φ i).1 i, ?_,
    fun z => Filter.limUnder Filter.atTop (fun i => J ((Φ i).1 i) z), ?_⟩
  · refine strictMono_nat_of_lt_succ fun i => ?_
    show (Φ i).1 i < (Φ (i + 1)).1 (i + 1)
    rw [hΦsucc i]
    have h1 : i + 1 ≤ τ (i + 1) (Φ i).1 (Φ i).2 (i + 1) :=
      (hτ1 (i + 1) (Φ i).1 (Φ i).2).le_apply
    exact lt_of_lt_of_le ((Φ i).2 (Nat.lt_succ_self i)) ((Φ i).2.monotone h1)
  · intro K hK hKc
    obtain ⟨j, hKj⟩ := hKxsuper K hK hKc
    obtain ⟨Lj, hLj⟩ := hstage j
    have hdiag : TendstoUniformlyOn (fun i => J ((Φ i).1 i)) Lj Filter.atTop (Kx j) := by
      rw [Metric.tendstoUniformlyOn_iff] at hLj ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hLj ε hε)
      refine Filter.eventually_atTop.mpr ⟨max j M, fun i hi z hz => ?_⟩
      obtain ⟨θ, hθ, hθeq⟩ := hfact j i (le_trans (le_max_left _ _) hi)
      show dist (Lj z) (J ((Φ i).1 i) z) < ε
      rw [hθeq i]
      exact hM (θ i) (le_trans (le_trans (le_max_right _ _) hi) (hθ i)) z hz
    refine (hdiag.congr_right fun z hz => ?_).mono hKj
    exact ((hdiag.tendsto_at hz).limUnder_eq).symm
